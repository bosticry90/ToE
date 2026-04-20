from __future__ import annotations

import argparse
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_CYCLE11_EXPLICIT_DOWNSTREAM_AUTHORIZATION_REPORT_20260419_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "QM_STAT_CYCLE11_EXPLICIT_DOWNSTREAM_AUTHORIZATION_20260419_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "qm_stat_cycle11_explicit_downstream_authorization_20260419_v0.json"
)


def _read(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _has_token(text: str, token: str) -> bool:
    pattern = re.compile(rf"(?m)^\s*(?:[-*]\s+)?`?{re.escape(token)}`?\s*$")
    return bool(pattern.search(text))


def _row_entry(rows: list[dict[str, Any]], row_id: str) -> dict[str, Any]:
    for row in rows:
        if str(row.get("row_id", "")).strip() == row_id:
            return dict(row)
    return {}


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    target_seam = dict(declaration.get("target_seam", {}))
    required_inputs = dict(declaration.get("required_inputs", {}))
    contract = dict(declaration.get("downstream_authorization_contract", {}))
    outcome_contract = dict(declaration.get("downstream_authorization_outcome_contract", {}))

    pre_screening_path = REPO_ROOT / str(required_inputs.get("qm_stat_cycle11_pre_screening_step_report", "")).strip()
    readiness_path = REPO_ROOT / str(required_inputs.get("qm_stat_seam_authorization_readiness_dossier_report", "")).strip()
    lane_status_path = REPO_ROOT / str(required_inputs.get("qm_stat_cycle11_lane_status_report", "")).strip()
    physics_progress_path = REPO_ROOT / str(required_inputs.get("physics_progress_ledger_report", "")).strip()
    sla_path = REPO_ROOT / str(required_inputs.get("seam_resolution_sla_ledger_report", "")).strip()
    candidate_doc_path = REPO_ROOT / str(required_inputs.get("cycle12_candidate_doc", "")).strip()
    target_doc_path = REPO_ROOT / str(required_inputs.get("cycle12_target_doc", "")).strip()
    artifact_path = REPO_ROOT / str(required_inputs.get("cycle12_artifact", "")).strip()
    gate_path = REPO_ROOT / str(required_inputs.get("cycle12_gate", "")).strip()

    pre_screening = _read_json(pre_screening_path)
    readiness = _read_json(readiness_path)
    lane_status = _read_json(lane_status_path)
    physics_progress = _read_json(physics_progress_path)
    sla = _read_json(sla_path)
    candidate_doc = _read(candidate_doc_path)
    target_doc = _read(target_doc_path)
    artifact = _read_json(artifact_path)
    gate_exists = gate_path.exists()

    pre_screening_summary = dict(pre_screening.get("summary", {}))
    readiness_summary = dict(readiness.get("summary", {}))
    lane_summary = dict(lane_status.get("summary", {}))
    target_row_id = str(target_seam.get("row_id", "")).strip()
    target_lane = str(target_seam.get("lane", "")).strip()
    sla_entry = _row_entry(list(sla.get("entries", [])), target_row_id)

    candidate_tokens_ok = all(_has_token(candidate_doc, token) for token in contract.get("required_candidate_tokens", []))
    target_doc_tokens_ok = all(_has_token(target_doc, token) for token in contract.get("required_target_doc_tokens", []))
    artifact_basis_ok = all(
        [
            str(artifact.get("status", "")).strip() == str(contract.get("required_artifact_status", "")).strip(),
            str(dict(artifact.get("adjudication", {})).get("value", "")).strip()
            == str(contract.get("required_adjudication", "")).strip(),
            str(artifact.get("artifact_id", "")).strip() == "qm_stat_class_b_seam_physics_pilot_cycle12_v0",
        ]
    )

    minimum_tranche = dict(contract.get("minimum_bounded_downstream_tranche", {}))
    tranche_shape_ok = all(
        key in minimum_tranche
        for key in [
            "target_row_id",
            "source_lane",
            "authorized_candidate_target",
            "current_status",
            "required_evidence_surface",
            "required_closure_artifact",
            "required_closure_gate",
            "required_exit_criterion",
            "bounded_scope",
        ]
    )

    preconditions_ok = all(
        [
            str(pre_screening_summary.get("terminal_outcome", "")).strip()
            == str(contract.get("required_pre_screening_outcome", "")).strip(),
            str(pre_screening_summary.get("next_action", "")).strip()
            == str(contract.get("required_pre_screening_next_action", "")).strip(),
            str(pre_screening_summary.get("target_row_id", "")).strip() == target_row_id,
            str(pre_screening_summary.get("target_lane", "")).strip() == target_lane,
            str(readiness_summary.get("terminal_outcome", "")).strip()
            == str(contract.get("required_readiness_outcome", "")).strip(),
            str(readiness_summary.get("target_row_id", "")).strip() == target_row_id,
            str(readiness_summary.get("target_lane", "")).strip() == target_lane,
            str(lane_summary.get("internal_lane_status", "")).strip()
            == str(contract.get("required_lane_internal_status", "")).strip(),
            str(lane_summary.get("externalization_status", "")).strip()
            == str(contract.get("required_lane_externalization_status", "")).strip(),
            str(physics_progress.get("progress_classification", "")).strip()
            == str(contract.get("required_progress_classification", "")).strip(),
            str(sla_entry.get("decision_state", "")).strip()
            == str(contract.get("required_sla_decision_state", "")).strip(),
            str(sla_entry.get("gate_runtime_status", "")).strip()
            == str(contract.get("required_sla_gate_runtime_status", "")).strip(),
            str(sla_entry.get("target_surface", "")).strip()
            == str(readiness.get("target_row_dossier", {}).get("minimum_post_authorization_tranche", {}).get("required_evidence_surface", "")).strip(),
            candidate_tokens_ok,
            target_doc_tokens_ok,
            artifact_basis_ok,
            gate_exists,
            str(minimum_tranche.get("target_row_id", "")).strip() == target_row_id,
            str(minimum_tranche.get("source_lane", "")).strip() == target_lane,
            str(minimum_tranche.get("required_evidence_surface", "")).strip() == _ptr(target_doc_path),
            str(minimum_tranche.get("required_closure_artifact", "")).strip() == _ptr(artifact_path),
            str(minimum_tranche.get("required_closure_gate", "")).strip() == _ptr(gate_path),
            str(minimum_tranche.get("current_status", "")).strip()
            == str(contract.get("required_sla_gate_runtime_status", "")).strip(),
            tranche_shape_ok,
        ]
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get("default_outcome", "QM_STAT_EXPLICIT_DOWNSTREAM_AUTHORIZATION_EVIDENCE_INCOMPLETE")
    ).strip()

    if not tranche_shape_ok or not gate_exists:
        terminal_outcome = "HOLD_PENDING_QM_STAT_EXPLICIT_DOWNSTREAM_AUTHORIZATION_REPAIR"
        next_action = "REPAIR_QM_STAT_EXPLICIT_DOWNSTREAM_AUTHORIZATION_SHAPE"
    elif preconditions_ok:
        terminal_outcome = str(contract.get("authorization_result_token", "")).strip()
        next_action = "EXECUTE_ONE_BOUNDED_QM_STAT_CYCLE12_CONTINUATION_ONLY"
    elif str(pre_screening_summary.get("terminal_outcome", "")).strip() != str(
        contract.get("required_pre_screening_outcome", "")
    ).strip():
        terminal_outcome = "QM_STAT_EXPLICIT_DOWNSTREAM_AUTHORIZATION_BLOCKED"
        next_action = "RESTORE_QM_STAT_CYCLE11_PRE_SCREENING_STOP_TOKEN_BEFORE_DOWNSTREAM_AUTHORIZATION"
    else:
        terminal_outcome = "QM_STAT_EXPLICIT_DOWNSTREAM_AUTHORIZATION_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_QM_STAT_DOWNSTREAM_AUTHORIZATION_PRECONDITIONS_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "pre_screening_stop_token_matches": str(pre_screening_summary.get("terminal_outcome", "")).strip()
            == str(contract.get("required_pre_screening_outcome", "")).strip(),
            "readiness_outcome_matches": str(readiness_summary.get("terminal_outcome", "")).strip()
            == str(contract.get("required_readiness_outcome", "")).strip(),
            "lane_internal_status_matches": str(lane_summary.get("internal_lane_status", "")).strip()
            == str(contract.get("required_lane_internal_status", "")).strip(),
            "lane_externalization_matches": str(lane_summary.get("externalization_status", "")).strip()
            == str(contract.get("required_lane_externalization_status", "")).strip(),
            "candidate_tokens_present": candidate_tokens_ok,
            "target_doc_tokens_present": target_doc_tokens_ok,
            "artifact_basis_ok": artifact_basis_ok,
            "gate_exists": gate_exists,
            "minimum_bounded_downstream_tranche_shape_ok": tranche_shape_ok,
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_QM_STAT_CYCLE11_EXPLICIT_DOWNSTREAM_AUTHORIZATION_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_QM_STAT_CYCLE11_EXPLICIT_DOWNSTREAM_AUTHORIZATION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "downstream_authorization_preconditions_satisfied": preconditions_ok,
                "single_path_nonlive_boundary_preserved": int(contract.get("execution_live_token_count", 0)) == 0,
            },
            "inputs": {
                "target_row_id": target_row_id,
                "source_lane": target_lane,
                "authorized_candidate_target": minimum_tranche.get("authorized_candidate_target"),
                "pre_screening_terminal_outcome": pre_screening_summary.get("terminal_outcome"),
                "pre_screening_next_action": pre_screening_summary.get("next_action"),
                "readiness_terminal_outcome": readiness_summary.get("terminal_outcome"),
                "lane_internal_status": lane_summary.get("internal_lane_status"),
                "lane_externalization_status": lane_summary.get("externalization_status"),
                "progress_classification": physics_progress.get("progress_classification"),
                "authorization_scope_token": contract.get("authorization_scope_token"),
                "execution_live_token_count": contract.get("execution_live_token_count"),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "target_row_id": target_row_id,
            "source_lane": target_lane,
            "authorized_candidate_target": minimum_tranche.get("authorized_candidate_target"),
            "authorization_scope_token": contract.get("authorization_scope_token"),
            "authorization_result_token": contract.get("authorization_result_token"),
            "branch_chain_status": contract.get("branch_chain_status"),
            "execution_live_token_count": contract.get("execution_live_token_count"),
            "selected_candidate_artifact_pointer": _ptr(candidate_doc_path),
            "selected_target_artifact_pointer": _ptr(artifact_path),
            "selected_target_gate_pointer": _ptr(gate_path),
            "next_action": next_action,
            "single_layer_only": bool(contract.get("single_layer_only", True)),
            "single_outcome_only": bool(contract.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "qm_stat_cycle11_pre_screening_step_report": _ptr(pre_screening_path),
            "qm_stat_seam_authorization_readiness_dossier_report": _ptr(readiness_path),
            "qm_stat_cycle11_lane_status_report": _ptr(lane_status_path),
            "physics_progress_ledger_report": _ptr(physics_progress_path),
            "seam_resolution_sla_ledger_report": _ptr(sla_path),
            "cycle12_candidate_doc": _ptr(candidate_doc_path),
            "cycle12_target_doc": _ptr(target_doc_path),
            "cycle12_artifact": _ptr(artifact_path),
            "cycle12_gate": _ptr(gate_path),
        },
        "non_claim_boundary": "Repository-local QM-STAT explicit downstream authorization report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the QM-STAT Cycle11 explicit downstream authorization report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    declaration_path = ns.declaration if ns.declaration.is_absolute() else (REPO_ROOT / ns.declaration)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(declaration_path=declaration_path, captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "qm_stat_cycle11_explicit_downstream_authorization_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())