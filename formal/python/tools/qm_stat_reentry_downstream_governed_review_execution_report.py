from __future__ import annotations

import argparse
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_EXECUTION_REPORT_20260420_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_EXECUTION_20260420_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "qm_stat_reentry_downstream_governed_review_execution_20260420_v0.json"
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
    contract = dict(declaration.get("governed_review_execution_contract", {}))
    outcome_contract = dict(declaration.get("governed_review_execution_outcome_contract", {}))

    packet_report_path = REPO_ROOT / str(required_inputs.get("downstream_governed_review_packet_report", "")).strip()
    adjudication_path = REPO_ROOT / str(required_inputs.get("reentry_post_review_adjudication_report", "")).strip()
    reentry_execution_path = REPO_ROOT / str(required_inputs.get("reentry_review_execution_report", "")).strip()
    promotion_policy_path = REPO_ROOT / str(required_inputs.get("promotion_governance_lane_policy", "")).strip()
    canonical_standard_path = REPO_ROOT / str(required_inputs.get("canonical_action_promotion_standard", "")).strip()

    packet_report = _read_json(packet_report_path)
    adjudication = _read_json(adjudication_path)
    reentry_execution = _read_json(reentry_execution_path)
    promotion_policy_text = _read(promotion_policy_path)
    canonical_standard_text = _read(canonical_standard_path)

    packet_summary = dict(packet_report.get("summary", {}))
    packet_criteria = dict(packet_report.get("criteria", {}))
    adjudication_summary = dict(adjudication.get("summary", {}))
    adjudication_criteria = dict(adjudication.get("criteria", {}))
    reentry_execution_summary = dict(reentry_execution.get("summary", {}))
    reentry_execution_criteria = dict(reentry_execution.get("criteria", {}))

    target_row_id = str(target_surface.get("row_id", "")).strip()
    target_seam_id = str(target_surface.get("seam_id", "")).strip()
    source_lane = str(target_surface.get("source_lane", "")).strip()
    target_package_id = str(target_surface.get("target_package_id", "")).strip()
    authorized_candidate_target = str(target_surface.get("authorized_candidate_target", "")).strip()

    promotion_policy_ok = all(_has_token(promotion_policy_text, token) for token in contract.get("required_promotion_policy_tokens", []))
    canonical_boundary_ok = all(_has_token(canonical_standard_text, token) for token in contract.get("required_canonical_action_tokens", []))

    preconditions_ok = all(
        [
            packet_summary.get("terminal_outcome") == str(contract.get("required_packet_outcome", "")).strip(),
            packet_summary.get("packet_decision") == str(contract.get("required_packet_decision", "")).strip(),
            packet_summary.get("next_action") == str(contract.get("required_packet_next_action", "")).strip(),
            packet_summary.get("authorization_scope_token") == str(contract.get("required_authorization_scope_token", "")).strip(),
            packet_summary.get("target_row_id") == target_row_id,
            packet_summary.get("target_seam_id") == target_seam_id,
            packet_summary.get("target_package_id") == target_package_id,
            packet_criteria.get("authorization_present") is True,
            packet_criteria.get("retained_candidate_preserved") is True,
            packet_criteria.get("review_completion_preserved") is True,
            adjudication_summary.get("post_review_adjudication") == str(contract.get("required_post_review_adjudication", "")).strip(),
            adjudication_summary.get("candidate_disposition") == str(contract.get("required_candidate_disposition", "")).strip(),
            adjudication_summary.get("target_row_id") == target_row_id,
            adjudication_summary.get("target_seam_id") == target_seam_id,
            adjudication_summary.get("target_package_id") == target_package_id,
            adjudication_criteria.get("binding_preserved") is True,
            adjudication_criteria.get("review_completed_without_canonical_action") is True,
            reentry_execution_summary.get("terminal_outcome") == str(contract.get("required_reentry_review_terminal_outcome", "")).strip(),
            reentry_execution_summary.get("review_decision") == str(contract.get("required_reentry_review_decision", "")).strip(),
            reentry_execution_summary.get("target_row_id") == target_row_id,
            reentry_execution_summary.get("target_seam_id") == target_seam_id,
            reentry_execution_summary.get("target_package_id") == target_package_id,
            reentry_execution_criteria.get("packet_ready") is True,
            reentry_execution_criteria.get("canonical_action_boundary_present") is True,
            promotion_policy_ok,
            canonical_boundary_ok,
        ]
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get("default_outcome", "QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_EVIDENCE_INCOMPLETE")
    ).strip()

    if not all([promotion_policy_ok, canonical_boundary_ok]):
        terminal_outcome = "HOLD_PENDING_QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_EXECUTION_REPAIR"
        next_action = "REPAIR_QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_EXECUTION_SHAPE"
    elif preconditions_ok:
        terminal_outcome = "QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_EXECUTED_NONLIVE"
        next_action = "STOP_AT_QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_EXECUTION_TOKEN_PENDING_ANY_FURTHER_GOVERNANCE_AUTHORIZATION"
    elif packet_summary.get("terminal_outcome") != str(contract.get("required_packet_outcome", "")).strip():
        terminal_outcome = "QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_BLOCKED"
        next_action = "RESTORE_QM_STAT_DOWNSTREAM_GOVERNED_REVIEW_PACKET_READY_STATE_BEFORE_EXECUTION"
    else:
        terminal_outcome = "QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_EXECUTION_PRECONDITIONS_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "packet_ready": packet_summary.get("terminal_outcome") == str(contract.get("required_packet_outcome", "")).strip(),
            "post_review_adjudication_preserved": adjudication_summary.get("post_review_adjudication") == str(contract.get("required_post_review_adjudication", "")).strip(),
            "review_completion_preserved": reentry_execution_summary.get("terminal_outcome") == str(contract.get("required_reentry_review_terminal_outcome", "")).strip(),
            "target_binding_preserved": adjudication_summary.get("target_row_id") == target_row_id and adjudication_summary.get("target_seam_id") == target_seam_id,
            "promotion_policy_tokens_present": promotion_policy_ok,
            "canonical_action_boundary_present": canonical_boundary_ok,
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip() == "EXACTLY_ONE_ALLOWED_QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_EXECUTION_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip() == "ONE_QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_EXECUTION_LAYER_ONLY"
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "governed_review_execution_preconditions_satisfied": preconditions_ok,
                "nonlive_boundary_preserved": int(contract.get("execution_live_token_count", 0)) == 0,
                "canonical_mutation_withheld": True
            },
            "inputs": {
                "target_row_id": target_row_id,
                "target_seam_id": target_seam_id,
                "source_lane": source_lane,
                "authorized_candidate_target": authorized_candidate_target,
                "target_package_id": target_package_id,
                "packet_terminal_outcome": packet_summary.get("terminal_outcome"),
                "post_review_adjudication": adjudication_summary.get("post_review_adjudication"),
                "reentry_review_terminal_outcome": reentry_execution_summary.get("terminal_outcome"),
                "execution_scope_token": contract.get("execution_scope_token"),
                "execution_live_token_count": contract.get("execution_live_token_count")
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action
            }
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "review_decision": "bounded_downstream_governed_review_executed_with_no_canonical_action" if terminal_outcome == "QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_EXECUTED_NONLIVE" else "bounded_downstream_governed_review_not_executed",
            "target_row_id": target_row_id,
            "target_seam_id": target_seam_id,
            "source_lane": source_lane,
            "authorized_candidate_target": authorized_candidate_target,
            "target_package_id": target_package_id,
            "execution_scope_token": contract.get("execution_scope_token"),
            "execution_live_token_count": contract.get("execution_live_token_count"),
            "authorization_scope_token": packet_summary.get("authorization_scope_token"),
            "canonical_mutation_emitted": False,
            "next_action": next_action,
            "single_layer_only": bool(contract.get("single_layer_only", True)),
            "single_outcome_only": bool(contract.get("single_outcome_only", True))
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "downstream_governed_review_packet_report": _ptr(packet_report_path),
            "reentry_post_review_adjudication_report": _ptr(adjudication_path),
            "reentry_review_execution_report": _ptr(reentry_execution_path),
            "promotion_governance_lane_policy": _ptr(promotion_policy_path),
            "canonical_action_promotion_standard": _ptr(canonical_standard_path)
        },
        "non_claim_boundary": "Repository-local QM-STAT downstream governed review execution report only; no canonical mutation, seam closure, or scientific adequacy claim."
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the QM-STAT downstream governed review execution report.")
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
        "qm_stat_reentry_downstream_governed_review_execution_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())