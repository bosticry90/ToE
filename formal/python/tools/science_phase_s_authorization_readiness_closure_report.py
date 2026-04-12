from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_PHASE_S_AUTHORIZATION_READINESS_CLOSURE_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_PHASE_S_AUTHORIZATION_READINESS_CLOSURE_20260412_v0.json"
)


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    readiness_contract = dict(declaration.get("authorization_readiness_contract", {}))
    outcome_contract = dict(declaration.get("authorization_readiness_outcome_contract", {}))

    phase_r_path = REPO_ROOT / str(
        required_inputs.get("science_phase_r_signal_produced_threshold_closure_report", "")
    ).strip()
    phase_o_path = REPO_ROOT / str(
        required_inputs.get("science_phase_o_authorized_candidate_next_step_selection_report", "")
    ).strip()
    non_reopen_summary_path = REPO_ROOT / str(
        required_inputs.get("science_closed_lane_non_reopen_reason_summary_report", "")
    ).strip()

    phase_r = _read_json(phase_r_path)
    phase_o = _read_json(phase_o_path)
    non_reopen_summary = _read_json(non_reopen_summary_path)

    phase_r_summary = dict(phase_r.get("summary", {}))
    phase_o_summary = dict(phase_o.get("summary", {}))

    phase_r_outcome = str(phase_r_summary.get("terminal_outcome", "")).strip()
    phase_r_authorized_lane_id = str(phase_r_summary.get("authorized_lane_id", "")).strip()
    phase_r_packet_authorization = bool(phase_r_summary.get("authorize_first_test_packet", True))
    phase_o_outcome = str(phase_o_summary.get("terminal_outcome", "")).strip()
    non_reopen_summary_outcome = str(
        dict(non_reopen_summary.get("summary", {})).get("terminal_outcome", "")
    ).strip()

    required_phase_r_outcome = str(readiness_contract.get("required_phase_r_outcome", "")).strip()
    required_phase_r_authorized_lane_id = str(
        readiness_contract.get("required_phase_r_authorized_lane_id", "")
    ).strip()
    required_phase_r_packet_authorization = bool(
        readiness_contract.get("required_phase_r_packet_authorization", False)
    )
    required_phase_o_outcome = str(readiness_contract.get("required_phase_o_outcome", "")).strip()
    required_non_reopen_summary_outcome = str(
        readiness_contract.get("required_non_reopen_summary_outcome", "")
    ).strip()
    forbid_reopen = bool(readiness_contract.get("forbid_closed_or_held_lane_reopen", False))

    readiness = dict(readiness_contract.get("authorization_readiness", {}))
    remaining_phase_o_fields_resolved = bool(readiness.get("remaining_phase_o_fields_resolved", False))
    authorization_review_ready = bool(readiness.get("authorization_review_ready", False))
    policy_compliance_bundle_complete = bool(readiness.get("policy_compliance_bundle_complete", False))
    candidate_preservation_status_confirmed = bool(
        readiness.get("candidate_preservation_status_confirmed", False)
    )
    packet_execution_still_separate = bool(readiness.get("packet_execution_still_separate", False))

    readiness_shape_ok = all(
        key in readiness
        for key in [
            "remaining_phase_o_fields_resolved",
            "authorization_review_ready",
            "policy_compliance_bundle_complete",
            "candidate_preservation_status_confirmed",
            "packet_execution_still_separate",
        ]
    )

    preconditions_ok = (
        phase_r_outcome == required_phase_r_outcome
        and phase_r_authorized_lane_id == required_phase_r_authorized_lane_id
        and phase_r_packet_authorization == required_phase_r_packet_authorization
        and phase_o_outcome == required_phase_o_outcome
        and non_reopen_summary_outcome == required_non_reopen_summary_outcome
        and forbid_reopen
        and readiness_shape_ok
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get("default_outcome", "AUTHORIZATION_READINESS_EVIDENCE_INCOMPLETE")
    ).strip()

    if not readiness_shape_ok:
        terminal_outcome = "HOLD_PENDING_AUTHORIZATION_READINESS_REPAIR"
        next_action = "REPAIR_AUTHORIZATION_READINESS_SHAPE"
        authorize_first_test_packet = False
    elif not preconditions_ok:
        terminal_outcome = "AUTHORIZATION_READINESS_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_PHASE_S_PRECONDITIONS_AND_RERUN"
        authorize_first_test_packet = False
    elif not policy_compliance_bundle_complete:
        terminal_outcome = "CANDIDATE_WITHDRAWN"
        next_action = "WITHDRAW_CANDIDATE_UNTIL_POLICY_COMPLIANCE_BUNDLE_IS_REBUILT"
        authorize_first_test_packet = False
    elif not candidate_preservation_status_confirmed:
        terminal_outcome = "CANDIDATE_REQUIRES_HIGHER_LEVEL_POLICY"
        next_action = "ESCALATE_TO_HIGHER_LEVEL_POLICY_FOR_CANDIDATE_STATUS_RESOLUTION"
        authorize_first_test_packet = False
    elif remaining_phase_o_fields_resolved and authorization_review_ready and packet_execution_still_separate:
        terminal_outcome = "AUTHORIZATION_READINESS_COMPLETE_PACKET_AUTHORIZED"
        next_action = "AUTHORIZE_PACKET_OPENING_IN_NEXT_SEPARATE_EXECUTION_STEP"
        authorize_first_test_packet = True
    else:
        terminal_outcome = "AUTHORIZATION_READINESS_PARTIAL_HOLD"
        next_action = "RESOLVE_REMAINING_PHASE_O_FIELDS_AND_SET_AUTHORIZATION_REVIEW_READY"
        authorize_first_test_packet = False

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "phase_r_outcome_match": phase_r_outcome == required_phase_r_outcome,
            "phase_r_authorized_lane_id_match": phase_r_authorized_lane_id == required_phase_r_authorized_lane_id,
            "phase_r_packet_authorization_match": phase_r_packet_authorization == required_phase_r_packet_authorization,
            "phase_o_outcome_match": phase_o_outcome == required_phase_o_outcome,
            "non_reopen_summary_outcome_match": non_reopen_summary_outcome == required_non_reopen_summary_outcome,
            "forbid_closed_or_held_lane_reopen": forbid_reopen,
            "authorization_readiness_shape_ok": readiness_shape_ok,
            "single_terminal_outcome_rule_declared": str(
                outcome_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_S_AUTHORIZATION_READINESS_CLOSURE_OUTCOME",
            "no_loop_rule_declared": str(
                outcome_contract.get("no_loop_rule", "")
            ).strip()
            == "ONE_SCIENCE_PHASE_S_AUTHORIZATION_READINESS_CLOSURE_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "authorization_readiness_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "phase_r_outcome": phase_r_outcome,
                "required_phase_r_outcome": required_phase_r_outcome,
                "phase_r_authorized_lane_id": phase_r_authorized_lane_id,
                "required_phase_r_authorized_lane_id": required_phase_r_authorized_lane_id,
                "phase_r_packet_authorization": phase_r_packet_authorization,
                "required_phase_r_packet_authorization": required_phase_r_packet_authorization,
                "phase_o_outcome": phase_o_outcome,
                "required_phase_o_outcome": required_phase_o_outcome,
                "non_reopen_summary_outcome": non_reopen_summary_outcome,
                "required_non_reopen_summary_outcome": required_non_reopen_summary_outcome,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "authorization_readiness": readiness,
        "summary": {
            "terminal_outcome": terminal_outcome,
            "authorized_lane_id": required_phase_r_authorized_lane_id,
            "authorize_first_test_packet": authorize_first_test_packet,
            "next_action": next_action,
            "single_layer_only": bool(readiness_contract.get("single_layer_only", True)),
            "single_outcome_only": bool(readiness_contract.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_phase_r_signal_produced_threshold_closure_report": _ptr(phase_r_path),
            "science_phase_o_authorized_candidate_next_step_selection_report": _ptr(phase_o_path),
            "science_closed_lane_non_reopen_reason_summary_report": _ptr(non_reopen_summary_path),
        },
        "non_claim_boundary": "Repository-local authorization-readiness closure report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate Phase S authorization-readiness closure report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "science_phase_s_authorization_readiness_closure_20260412_v0.json",
    )
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
        "science_phase_s_authorization_readiness_closure_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']}"
        f" authorize_first_test_packet={payload['summary']['authorize_first_test_packet']}"
        f" out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())