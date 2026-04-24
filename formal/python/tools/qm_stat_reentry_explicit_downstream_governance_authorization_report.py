from __future__ import annotations

import argparse
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_REENTRY_EXPLICIT_DOWNSTREAM_GOVERNANCE_AUTHORIZATION_REPORT_20260420_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_REENTRY_EXPLICIT_DOWNSTREAM_GOVERNANCE_AUTHORIZATION_20260420_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "qm_stat_reentry_explicit_downstream_governance_authorization_20260420_v0.json"
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
    target_seam = dict(declaration.get("target_seam", {}))
    required_inputs = dict(declaration.get("required_inputs", {}))
    contract = dict(declaration.get("downstream_governance_authorization_contract", {}))
    outcome_contract = dict(declaration.get("downstream_governance_authorization_outcome_contract", {}))

    adjudication_path = REPO_ROOT / str(required_inputs.get("reentry_post_review_adjudication_report", "")).strip()
    execution_path = REPO_ROOT / str(required_inputs.get("reentry_review_execution_report", "")).strip()
    packet_path = REPO_ROOT / str(required_inputs.get("reentry_review_execution_packet_report", "")).strip()
    promotion_policy_path = REPO_ROOT / str(required_inputs.get("promotion_governance_lane_policy", "")).strip()
    canonical_standard_path = REPO_ROOT / str(required_inputs.get("canonical_action_promotion_standard", "")).strip()
    state_surface_path = REPO_ROOT / str(required_inputs.get("state_surface", "")).strip()

    adjudication = _read_json(adjudication_path)
    execution = _read_json(execution_path)
    packet = _read_json(packet_path)
    promotion_policy_text = _read(promotion_policy_path)
    canonical_standard_text = _read(canonical_standard_path)
    state_surface_text = _read(state_surface_path)

    adjudication_summary = dict(adjudication.get("summary", {}))
    adjudication_criteria = dict(adjudication.get("criteria", {}))
    execution_summary = dict(execution.get("summary", {}))
    execution_criteria = dict(execution.get("criteria", {}))
    packet_summary = dict(packet.get("summary", {}))

    target_row_id = str(target_seam.get("row_id", "")).strip()
    target_seam_id = str(target_seam.get("seam_id", "")).strip()
    target_lane = str(target_seam.get("lane", "")).strip()

    promotion_policy_ok = all(
        _has_token(promotion_policy_text, token) for token in contract.get("required_promotion_policy_tokens", [])
    )
    canonical_standard_ok = all(
        _has_token(canonical_standard_text, token) for token in contract.get("required_canonical_action_tokens", [])
    )
    required_state_token = str(contract.get("required_state_next_action_token", "")).strip()
    authorized_next_action = str(
        contract.get("authorized_next_action", "AUTHOR_ONE_BOUNDED_QM_STAT_DOWNSTREAM_GOVERNED_REVIEW_PACKET_WITHOUT_CANONICAL_MUTATION")
    ).strip()
    authorized_state_token = f"RESEARCH_MODE_NEXT_ACTION_v0: {authorized_next_action}"
    explicit_authorization_tokens = [
        required_state_token,
        authorized_state_token,
        f"QM_STAT_REENTRY_EXPLICIT_DOWNSTREAM_GOVERNANCE_AUTHORIZATION_NEXT_ACTION_v0: {authorized_next_action}",
        "QM_STAT_REENTRY_EXPLICIT_DOWNSTREAM_GOVERNANCE_AUTHORIZATION_OUTCOME_v0: "
        + str(contract.get("authorization_result_token", "")).strip(),
        "QM_STAT_REENTRY_EXPLICIT_DOWNSTREAM_GOVERNANCE_AUTHORIZATION_SCOPE_v0: "
        + str(contract.get("authorization_scope_token", "")).strip(),
    ]
    state_token_ok = any(
        token and _has_token(state_surface_text, token)
        for token in explicit_authorization_tokens
    )

    tranche = dict(contract.get("minimum_bounded_downstream_tranche", {}))
    tranche_shape_ok = all(
        key in tranche
        for key in [
            "target_row_id",
            "target_seam_id",
            "source_lane",
            "authorized_candidate_target",
            "required_governance_policy",
            "required_boundary_standard",
            "required_exit_criterion",
            "bounded_scope",
        ]
    )

    preconditions_ok = all(
        [
            adjudication_summary.get("post_review_adjudication") == str(contract.get("required_post_review_adjudication", "")).strip(),
            adjudication_summary.get("candidate_disposition") == str(contract.get("required_candidate_disposition", "")).strip(),
            adjudication_summary.get("next_action") == str(contract.get("required_post_review_next_action", "")).strip(),
            adjudication_summary.get("target_row_id") == target_row_id,
            adjudication_summary.get("target_seam_id") == target_seam_id,
            adjudication_criteria.get("binding_preserved") is True,
            adjudication_criteria.get("governance_hold_supported") is True,
            execution_summary.get("terminal_outcome") == str(contract.get("required_review_terminal_outcome", "")).strip(),
            execution_summary.get("review_decision") == str(contract.get("required_review_decision", "")).strip(),
            execution_summary.get("target_row_id") == target_row_id,
            execution_summary.get("target_seam_id") == target_seam_id,
            execution_criteria.get("packet_ready") is True,
            execution_criteria.get("intake_acceptance_present") is True,
            execution_criteria.get("canonical_action_boundary_present") is True,
            packet_summary.get("terminal_outcome") == str(contract.get("required_packet_terminal_outcome", "")).strip(),
            packet_summary.get("packet_decision") == str(contract.get("required_packet_decision", "")).strip(),
            packet_summary.get("target_row_id") == target_row_id,
            packet_summary.get("target_seam_id") == target_seam_id,
            promotion_policy_ok,
            canonical_standard_ok,
            state_token_ok,
            tranche_shape_ok,
            str(tranche.get("target_row_id", "")).strip() == target_row_id,
            str(tranche.get("target_seam_id", "")).strip() == target_seam_id,
            str(tranche.get("source_lane", "")).strip() == target_lane,
            str(tranche.get("required_governance_policy", "")).strip() == _ptr(promotion_policy_path),
            str(tranche.get("required_boundary_standard", "")).strip() == _ptr(canonical_standard_path),
        ]
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get("default_outcome", "QM_STAT_REENTRY_DOWNSTREAM_GOVERNANCE_AUTHORIZATION_EVIDENCE_INCOMPLETE")
    ).strip()

    if not tranche_shape_ok:
        terminal_outcome = "HOLD_PENDING_QM_STAT_REENTRY_DOWNSTREAM_GOVERNANCE_AUTHORIZATION_REPAIR"
        next_action = "REPAIR_QM_STAT_REENTRY_DOWNSTREAM_GOVERNANCE_AUTHORIZATION_SHAPE"
    elif preconditions_ok:
        terminal_outcome = str(contract.get("authorization_result_token", "")).strip()
        next_action = authorized_next_action
    elif adjudication_summary.get("post_review_adjudication") != str(contract.get("required_post_review_adjudication", "")).strip():
        terminal_outcome = "QM_STAT_REENTRY_DOWNSTREAM_GOVERNANCE_AUTHORIZATION_BLOCKED"
        next_action = "RESTORE_RETAINED_REENTRY_REVIEWED_CANDIDATE_POSTURE_BEFORE_DOWNSTREAM_GOVERNANCE_AUTHORIZATION"
    else:
        terminal_outcome = "QM_STAT_REENTRY_DOWNSTREAM_GOVERNANCE_AUTHORIZATION_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_QM_STAT_REENTRY_DOWNSTREAM_GOVERNANCE_AUTHORIZATION_PRECONDITIONS_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "reentry_post_review_adjudication_matches": adjudication_summary.get("post_review_adjudication")
            == str(contract.get("required_post_review_adjudication", "")).strip(),
            "reentry_review_execution_matches": execution_summary.get("terminal_outcome")
            == str(contract.get("required_review_terminal_outcome", "")).strip(),
            "execution_packet_matches": packet_summary.get("terminal_outcome")
            == str(contract.get("required_packet_terminal_outcome", "")).strip(),
            "promotion_policy_tokens_present": promotion_policy_ok,
            "canonical_boundary_tokens_present": canonical_standard_ok,
            "state_next_action_token_present": state_token_ok,
            "minimum_bounded_downstream_tranche_shape_ok": tranche_shape_ok,
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_QM_STAT_REENTRY_EXPLICIT_DOWNSTREAM_GOVERNANCE_AUTHORIZATION_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_QM_STAT_REENTRY_EXPLICIT_DOWNSTREAM_GOVERNANCE_AUTHORIZATION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "downstream_governance_authorization_preconditions_satisfied": preconditions_ok,
                "single_path_nonlive_boundary_preserved": int(contract.get("execution_live_token_count", 0)) == 0,
                "canonical_mutation_withheld": True,
            },
            "inputs": {
                "target_row_id": target_row_id,
                "target_seam_id": target_seam_id,
                "source_lane": target_lane,
                "authorized_candidate_target": tranche.get("authorized_candidate_target"),
                "post_review_adjudication": adjudication_summary.get("post_review_adjudication"),
                "review_terminal_outcome": execution_summary.get("terminal_outcome"),
                "review_packet_terminal_outcome": packet_summary.get("terminal_outcome"),
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
            "target_seam_id": target_seam_id,
            "source_lane": target_lane,
            "authorized_candidate_target": tranche.get("authorized_candidate_target"),
            "authorization_scope_token": contract.get("authorization_scope_token"),
            "authorization_result_token": contract.get("authorization_result_token"),
            "branch_chain_status": contract.get("branch_chain_status"),
            "execution_live_token_count": contract.get("execution_live_token_count"),
            "next_action": next_action,
            "single_layer_only": bool(contract.get("single_layer_only", True)),
            "single_outcome_only": bool(contract.get("single_outcome_only", True)),
            "canonical_mutation_emitted": False,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "reentry_post_review_adjudication_report": _ptr(adjudication_path),
            "reentry_review_execution_report": _ptr(execution_path),
            "reentry_review_execution_packet_report": _ptr(packet_path),
            "promotion_governance_lane_policy": _ptr(promotion_policy_path),
            "canonical_action_promotion_standard": _ptr(canonical_standard_path),
            "state_surface": _ptr(state_surface_path),
        },
        "non_claim_boundary": "Repository-local QM-STAT reentry explicit downstream governance authorization report only; no canonical mutation or seam-closure claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the QM-STAT reentry explicit downstream governance authorization report.")
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
        "qm_stat_reentry_explicit_downstream_governance_authorization_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
