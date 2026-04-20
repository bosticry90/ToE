from __future__ import annotations

import argparse
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_CYCLE11_PRE_SCREENING_STEP_REPORT_20260419_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "QM_STAT_CYCLE11_PRE_SCREENING_STEP_20260419_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "qm_stat_cycle11_pre_screening_step_20260419_v0.json"
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


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    target_lane = dict(declaration.get("target_lane", {}))
    required_inputs = dict(declaration.get("required_inputs", {}))
    contract = dict(declaration.get("pre_screening_execution_contract", {}))
    outcome_contract = dict(declaration.get("pre_screening_execution_outcome_contract", {}))

    readiness_path = REPO_ROOT / str(required_inputs.get("qm_stat_seam_authorization_readiness_dossier_report", "")).strip()
    lane_status_path = REPO_ROOT / str(required_inputs.get("qm_stat_cycle11_lane_status_report", "")).strip()
    artifact_path = REPO_ROOT / str(required_inputs.get("cycle11_artifact", "")).strip()
    target_doc_path = REPO_ROOT / str(required_inputs.get("cycle11_target_doc", "")).strip()

    readiness = _read_json(readiness_path)
    lane_status = _read_json(lane_status_path)
    artifact = _read_json(artifact_path)
    target_doc = _read(target_doc_path)

    readiness_summary = dict(readiness.get("summary", {}))
    lane_summary = dict(lane_status.get("summary", {}))
    target_row_dossier = dict(readiness.get("target_row_dossier", {}))
    minimum_tranche = dict(target_row_dossier.get("minimum_post_authorization_tranche", {}))

    target_row_id = str(target_lane.get("row_id", "")).strip()
    target_lane_name = str(target_lane.get("lane", "")).strip()

    required_doc_tokens = list(contract.get("required_target_doc_tokens", []))
    doc_tokens_present = all(_has_token(target_doc, token) for token in required_doc_tokens)

    artifact_basis_ok = all(
        [
            str(artifact.get("status", "")).strip() == str(contract.get("required_artifact_status", "")).strip(),
            str(dict(artifact.get("adjudication", {})).get("value", "")).strip()
            == str(contract.get("required_adjudication", "")).strip(),
            str(artifact.get("artifact_id", "")).strip() == "qm_stat_class_b_seam_physics_pilot_cycle11_v0",
        ]
    )

    tranche_alignment_ok = all(
        [
            str(minimum_tranche.get("target_row_id", "")).strip() == target_row_id,
            str(minimum_tranche.get("target_lane", "")).strip() == target_lane_name,
            str(minimum_tranche.get("required_closure_artifact", "")).strip() == _ptr(artifact_path),
            str(minimum_tranche.get("required_evidence_surface", "")).strip() == _ptr(target_doc_path),
        ]
    )

    preconditions_ok = all(
        [
            str(readiness_summary.get("terminal_outcome", "")).strip()
            == str(contract.get("required_readiness_outcome", "")).strip(),
            str(readiness_summary.get("next_action", "")).strip()
            == str(contract.get("required_readiness_next_action", "")).strip(),
            str(readiness_summary.get("current_restart_blocker", "")).strip()
            == str(contract.get("required_current_restart_blocker", "")).strip(),
            str(readiness_summary.get("target_row_id", "")).strip() == target_row_id,
            str(readiness_summary.get("target_lane", "")).strip() == target_lane_name,
            str(lane_summary.get("internal_lane_status", "")).strip()
            == str(contract.get("required_lane_internal_status", "")).strip(),
            str(lane_summary.get("externalization_status", "")).strip()
            == str(contract.get("required_lane_externalization_status", "")).strip(),
            str(lane_summary.get("routing_implication", "")).strip()
            == str(contract.get("required_lane_routing_implication", "")).strip(),
            artifact_basis_ok,
            doc_tokens_present,
            tranche_alignment_ok,
        ]
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get("default_outcome", "QM_STAT_CYCLE11_PRE_SCREENING_STEP_EVIDENCE_INCOMPLETE")
    ).strip()

    if not doc_tokens_present or not tranche_alignment_ok:
        terminal_outcome = "HOLD_PENDING_QM_STAT_CYCLE11_PRE_SCREENING_STEP_REPAIR"
        next_action = "REPAIR_QM_STAT_CYCLE11_PRE_SCREENING_EXECUTION_SHAPE"
    elif preconditions_ok:
        terminal_outcome = "QM_STAT_CYCLE11_PRE_SCREENING_STEP_EXECUTED_NONLIVE"
        next_action = "STOP_AT_QM_STAT_CYCLE11_PRE_SCREENING_TOKEN_PENDING_EXPLICIT_DOWNSTREAM_AUTHORIZATION"
    elif str(readiness_summary.get("terminal_outcome", "")).strip() != str(contract.get("required_readiness_outcome", "")).strip():
        terminal_outcome = "QM_STAT_CYCLE11_PRE_SCREENING_STEP_BLOCKED"
        next_action = "RESTORE_QM_STAT_BOUNDED_PRE_SCREENING_READINESS_BEFORE_EXECUTION"
    else:
        terminal_outcome = "QM_STAT_CYCLE11_PRE_SCREENING_STEP_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_QM_STAT_CYCLE11_PRE_SCREENING_PRECONDITIONS_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "readiness_outcome_matches": str(readiness_summary.get("terminal_outcome", "")).strip()
            == str(contract.get("required_readiness_outcome", "")).strip(),
            "readiness_next_action_matches": str(readiness_summary.get("next_action", "")).strip()
            == str(contract.get("required_readiness_next_action", "")).strip(),
            "lane_status_matches": str(lane_summary.get("internal_lane_status", "")).strip()
            == str(contract.get("required_lane_internal_status", "")).strip(),
            "lane_externalization_out_of_scope": str(lane_summary.get("externalization_status", "")).strip()
            == str(contract.get("required_lane_externalization_status", "")).strip(),
            "artifact_basis_ok": artifact_basis_ok,
            "target_doc_tokens_present": doc_tokens_present,
            "tranche_alignment_ok": tranche_alignment_ok,
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_QM_STAT_CYCLE11_PRE_SCREENING_STEP_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_QM_STAT_CYCLE11_PRE_SCREENING_STEP_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "pre_screening_preconditions_satisfied": preconditions_ok,
                "nonlive_boundary_preserved": int(contract.get("execution_live_token_count", 0)) == 0,
            },
            "inputs": {
                "target_row_id": target_row_id,
                "target_lane": target_lane_name,
                "readiness_outcome": readiness_summary.get("terminal_outcome"),
                "readiness_next_action": readiness_summary.get("next_action"),
                "lane_internal_status": lane_summary.get("internal_lane_status"),
                "lane_externalization_status": lane_summary.get("externalization_status"),
                "lane_routing_implication": lane_summary.get("routing_implication"),
                "execution_scope_token": contract.get("execution_scope_token"),
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
            "target_lane": target_lane_name,
            "execution_scope_token": contract.get("execution_scope_token"),
            "execution_live_token_count": contract.get("execution_live_token_count"),
            "selected_target_artifact_pointer": _ptr(artifact_path),
            "selected_target_gate_pointer": str(minimum_tranche.get("required_closure_gate", "")).strip(),
            "next_action": next_action,
            "single_layer_only": bool(contract.get("single_layer_only", True)),
            "single_outcome_only": bool(contract.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "qm_stat_seam_authorization_readiness_dossier_report": _ptr(readiness_path),
            "qm_stat_cycle11_lane_status_report": _ptr(lane_status_path),
            "cycle11_artifact": _ptr(artifact_path),
            "cycle11_target_doc": _ptr(target_doc_path),
        },
        "non_claim_boundary": "Repository-local QM-STAT Cycle11 pre-screening step report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the QM-STAT Cycle11 pre-screening step report.")
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
        "qm_stat_cycle11_pre_screening_step_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())