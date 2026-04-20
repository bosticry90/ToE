from __future__ import annotations

import argparse
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_CYCLE12_CONTINUATION_EXECUTION_REPORT_20260419_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "QM_STAT_CYCLE12_CONTINUATION_EXECUTION_20260419_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "qm_stat_cycle12_continuation_execution_20260419_v0.json"
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
    target_surface = dict(declaration.get("target_surface", {}))
    required_inputs = dict(declaration.get("required_inputs", {}))
    contract = dict(declaration.get("continuation_execution_contract", {}))
    outcome_contract = dict(declaration.get("continuation_execution_outcome_contract", {}))

    authorization_path = REPO_ROOT / str(
        required_inputs.get("qm_stat_cycle11_explicit_downstream_authorization_report", "")
    ).strip()
    candidate_doc_path = REPO_ROOT / str(required_inputs.get("cycle12_candidate_doc", "")).strip()
    target_doc_path = REPO_ROOT / str(required_inputs.get("cycle12_target_doc", "")).strip()
    artifact_path = REPO_ROOT / str(required_inputs.get("cycle12_artifact", "")).strip()
    gate_path = REPO_ROOT / str(required_inputs.get("cycle12_gate", "")).strip()

    authorization = _read_json(authorization_path)
    candidate_doc = _read(candidate_doc_path)
    target_doc = _read(target_doc_path)
    artifact = _read_json(artifact_path)
    gate_text = _read(gate_path)

    authorization_summary = dict(authorization.get("summary", {}))
    target_row_id = str(target_surface.get("row_id", "")).strip()
    source_lane = str(target_surface.get("source_lane", "")).strip()
    authorized_candidate_target = str(target_surface.get("authorized_candidate_target", "")).strip()

    candidate_tokens_ok = all(_has_token(candidate_doc, token) for token in contract.get("required_candidate_tokens", []))
    target_doc_tokens_ok = all(_has_token(target_doc, token) for token in contract.get("required_target_doc_tokens", []))
    gate_tokens_ok = all(token in gate_text for token in contract.get("required_gate_tokens", []))
    artifact_basis_ok = all(
        [
            str(artifact.get("status", "")).strip() == str(contract.get("required_artifact_status", "")).strip(),
            str(dict(artifact.get("adjudication", {})).get("value", "")).strip()
            == str(contract.get("required_adjudication", "")).strip(),
            str(artifact.get("artifact_id", "")).strip() == "qm_stat_class_b_seam_physics_pilot_cycle12_v0",
        ]
    )

    preconditions_ok = all(
        [
            str(authorization_summary.get("terminal_outcome", "")).strip()
            == str(contract.get("required_authorization_outcome", "")).strip(),
            str(authorization_summary.get("next_action", "")).strip()
            == str(contract.get("required_authorization_next_action", "")).strip(),
            str(authorization_summary.get("target_row_id", "")).strip() == target_row_id,
            str(authorization_summary.get("source_lane", "")).strip() == source_lane,
            str(authorization_summary.get("authorized_candidate_target", "")).strip() == authorized_candidate_target,
            str(authorization_summary.get("authorization_scope_token", "")).strip()
            == str(contract.get("required_authorization_scope_token", "")).strip(),
            str(authorization_summary.get("branch_chain_status", "")).strip()
            == str(contract.get("required_branch_chain_status", "")).strip(),
            candidate_tokens_ok,
            target_doc_tokens_ok,
            gate_tokens_ok,
            artifact_basis_ok,
            str(authorization_summary.get("selected_candidate_artifact_pointer", "")).strip() == _ptr(candidate_doc_path),
            str(authorization_summary.get("selected_target_artifact_pointer", "")).strip() == _ptr(artifact_path),
            str(authorization_summary.get("selected_target_gate_pointer", "")).strip() == _ptr(gate_path),
        ]
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get("default_outcome", "QM_STAT_CYCLE12_CONTINUATION_EVIDENCE_INCOMPLETE")
    ).strip()

    if not gate_tokens_ok or not candidate_tokens_ok or not target_doc_tokens_ok:
        terminal_outcome = "HOLD_PENDING_QM_STAT_CYCLE12_CONTINUATION_EXECUTION_REPAIR"
        next_action = "REPAIR_QM_STAT_CYCLE12_CONTINUATION_EXECUTION_SHAPE"
    elif preconditions_ok:
        terminal_outcome = "QM_STAT_CYCLE12_CONTINUATION_EXECUTED_NONLIVE"
        next_action = "STOP_AT_QM_STAT_CYCLE12_CONTINUATION_EXECUTION_TOKEN_PENDING_ANY_FURTHER_DOWNSTREAM_AUTHORIZATION"
    elif str(authorization_summary.get("terminal_outcome", "")).strip() != str(
        contract.get("required_authorization_outcome", "")
    ).strip():
        terminal_outcome = "QM_STAT_CYCLE12_CONTINUATION_BLOCKED"
        next_action = "RESTORE_QM_STAT_CYCLE12_SINGLE_LANE_AUTHORIZATION_BEFORE_CONTINUATION_EXECUTION"
    else:
        terminal_outcome = "QM_STAT_CYCLE12_CONTINUATION_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_QM_STAT_CYCLE12_CONTINUATION_PRECONDITIONS_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "authorization_outcome_matches": str(authorization_summary.get("terminal_outcome", "")).strip()
            == str(contract.get("required_authorization_outcome", "")).strip(),
            "authorization_next_action_matches": str(authorization_summary.get("next_action", "")).strip()
            == str(contract.get("required_authorization_next_action", "")).strip(),
            "authorization_scope_matches": str(authorization_summary.get("authorization_scope_token", "")).strip()
            == str(contract.get("required_authorization_scope_token", "")).strip(),
            "branch_chain_status_matches": str(authorization_summary.get("branch_chain_status", "")).strip()
            == str(contract.get("required_branch_chain_status", "")).strip(),
            "candidate_tokens_present": candidate_tokens_ok,
            "target_doc_tokens_present": target_doc_tokens_ok,
            "target_gate_tokens_present": gate_tokens_ok,
            "artifact_basis_ok": artifact_basis_ok,
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_QM_STAT_CYCLE12_CONTINUATION_EXECUTION_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_QM_STAT_CYCLE12_CONTINUATION_EXECUTION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "continuation_execution_preconditions_satisfied": preconditions_ok,
                "nonlive_boundary_preserved": int(contract.get("execution_live_token_count", 0)) == 0,
            },
            "inputs": {
                "target_row_id": target_row_id,
                "source_lane": source_lane,
                "authorized_candidate_target": authorized_candidate_target,
                "authorization_terminal_outcome": authorization_summary.get("terminal_outcome"),
                "authorization_next_action": authorization_summary.get("next_action"),
                "authorization_scope_token": authorization_summary.get("authorization_scope_token"),
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
            "source_lane": source_lane,
            "authorized_candidate_target": authorized_candidate_target,
            "execution_scope_token": contract.get("execution_scope_token"),
            "execution_live_token_count": contract.get("execution_live_token_count"),
            "selected_candidate_artifact_pointer": _ptr(candidate_doc_path),
            "selected_target_doc_pointer": _ptr(target_doc_path),
            "selected_target_artifact_pointer": _ptr(artifact_path),
            "selected_target_gate_pointer": _ptr(gate_path),
            "next_action": next_action,
            "single_layer_only": bool(contract.get("single_layer_only", True)),
            "single_outcome_only": bool(contract.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "qm_stat_cycle11_explicit_downstream_authorization_report": _ptr(authorization_path),
            "cycle12_candidate_doc": _ptr(candidate_doc_path),
            "cycle12_target_doc": _ptr(target_doc_path),
            "cycle12_artifact": _ptr(artifact_path),
            "cycle12_gate": _ptr(gate_path),
        },
        "non_claim_boundary": "Repository-local QM-STAT Cycle12 continuation execution report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the QM-STAT Cycle12 continuation execution report.")
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
        "qm_stat_cycle12_continuation_execution_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
