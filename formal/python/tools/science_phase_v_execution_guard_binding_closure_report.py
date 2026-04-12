from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_PHASE_V_EXECUTION_GUARD_BINDING_CLOSURE_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_PHASE_V_EXECUTION_GUARD_BINDING_CLOSURE_20260412_v0.json"
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
    contract = dict(declaration.get("execution_guard_binding_contract", {}))
    outcome_contract = dict(declaration.get("execution_guard_binding_outcome_contract", {}))

    phase_u_path = REPO_ROOT / str(
        required_inputs.get("science_phase_u_execution_guard_authorization_ready_closure_report", "")
    ).strip()
    phase_o_path = REPO_ROOT / str(
        required_inputs.get("science_phase_o_authorized_candidate_next_step_selection_report", "")
    ).strip()
    non_reopen_summary_path = REPO_ROOT / str(
        required_inputs.get("science_closed_lane_non_reopen_reason_summary_report", "")
    ).strip()

    phase_u = _read_json(phase_u_path)
    phase_o = _read_json(phase_o_path)
    non_reopen_summary = _read_json(non_reopen_summary_path)

    phase_u_summary = dict(phase_u.get("summary", {}))
    phase_o_summary = dict(phase_o.get("summary", {}))

    phase_u_outcome = str(phase_u_summary.get("terminal_outcome", "")).strip()
    phase_u_authorized_lane_id = str(phase_u_summary.get("authorized_lane_id", "")).strip()
    phase_u_packet_authorization = bool(phase_u_summary.get("authorize_first_test_packet", True))
    phase_o_outcome = str(phase_o_summary.get("terminal_outcome", "")).strip()
    non_reopen_summary_outcome = str(
        dict(non_reopen_summary.get("summary", {})).get("terminal_outcome", "")
    ).strip()

    required_phase_u_outcome = str(contract.get("required_phase_u_outcome", "")).strip()
    required_phase_u_authorized_lane_id = str(contract.get("required_phase_u_authorized_lane_id", "")).strip()
    required_phase_u_packet_authorization = bool(contract.get("required_phase_u_packet_authorization", False))
    required_phase_o_outcome = str(contract.get("required_phase_o_outcome", "")).strip()
    required_non_reopen_summary_outcome = str(contract.get("required_non_reopen_summary_outcome", "")).strip()
    forbid_reopen = bool(contract.get("forbid_closed_or_held_lane_reopen", False))

    closure = dict(contract.get("binding_closure", {}))
    execution_guard_binding_closed = bool(closure.get("execution_guard_binding_closed", False))
    authorization_review_ready = bool(closure.get("authorization_review_ready", False))
    packet_execution_still_separate = bool(closure.get("packet_execution_still_separate", False))
    policy_escalation_required = bool(closure.get("policy_escalation_required", False))
    candidate_preservation_status_confirmed = bool(
        closure.get("candidate_preservation_status_confirmed", False)
    )

    closure_shape_ok = all(
        key in closure
        for key in [
            "execution_guard_binding_closed",
            "authorization_review_ready",
            "packet_execution_still_separate",
            "policy_escalation_required",
            "candidate_preservation_status_confirmed",
        ]
    )

    preconditions_ok = (
        phase_u_outcome == required_phase_u_outcome
        and phase_u_authorized_lane_id == required_phase_u_authorized_lane_id
        and phase_u_packet_authorization == required_phase_u_packet_authorization
        and phase_o_outcome == required_phase_o_outcome
        and non_reopen_summary_outcome == required_non_reopen_summary_outcome
        and forbid_reopen
        and closure_shape_ok
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get("default_outcome", "EXECUTION_GUARD_BINDING_EVIDENCE_INCOMPLETE")
    ).strip()

    if not closure_shape_ok:
        terminal_outcome = "HOLD_PENDING_EXECUTION_GUARD_BINDING_REPAIR"
        next_action = "REPAIR_EXECUTION_GUARD_BINDING_SHAPE"
        authorize_first_test_packet = False
    elif not preconditions_ok:
        terminal_outcome = "EXECUTION_GUARD_BINDING_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_PHASE_V_PRECONDITIONS_AND_RERUN"
        authorize_first_test_packet = False
    elif not packet_execution_still_separate:
        terminal_outcome = "CANDIDATE_WITHDRAWN"
        next_action = "WITHDRAW_CANDIDATE_UNTIL_PACKET_EXECUTION_SEPARATION_IS_RESTORED"
        authorize_first_test_packet = False
    elif policy_escalation_required:
        terminal_outcome = "REQUIRES_HIGHER_LEVEL_POLICY"
        next_action = "ESCALATE_TO_HIGHER_LEVEL_POLICY_FOR_BINDING_DECISION"
        authorize_first_test_packet = False
    elif not candidate_preservation_status_confirmed:
        terminal_outcome = "CANDIDATE_WITHDRAWN"
        next_action = "WITHDRAW_CANDIDATE_UNTIL_PRESERVATION_STATUS_IS_RESTORED"
        authorize_first_test_packet = False
    elif execution_guard_binding_closed and authorization_review_ready:
        terminal_outcome = "EXECUTION_GUARD_BINDING_CLOSED_AND_PACKET_AUTHORIZED"
        next_action = "AUTHORIZE_PACKET_OPENING_IN_NEXT_SEPARATE_EXECUTION_STEP"
        authorize_first_test_packet = True
    else:
        terminal_outcome = "EXECUTION_GUARD_BINDING_PARTIAL_HOLD"
        next_action = "CLOSE_EXECUTION_GUARD_BINDING_AND_SET_AUTHORIZATION_REVIEW_READY"
        authorize_first_test_packet = False

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "phase_u_outcome_match": phase_u_outcome == required_phase_u_outcome,
            "phase_u_authorized_lane_id_match": phase_u_authorized_lane_id == required_phase_u_authorized_lane_id,
            "phase_u_packet_authorization_match": phase_u_packet_authorization == required_phase_u_packet_authorization,
            "phase_o_outcome_match": phase_o_outcome == required_phase_o_outcome,
            "non_reopen_summary_outcome_match": non_reopen_summary_outcome == required_non_reopen_summary_outcome,
            "forbid_closed_or_held_lane_reopen": forbid_reopen,
            "binding_closure_shape_ok": closure_shape_ok,
            "single_terminal_outcome_rule_declared": str(
                outcome_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_V_EXECUTION_GUARD_BINDING_CLOSURE_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_SCIENCE_PHASE_V_EXECUTION_GUARD_BINDING_CLOSURE_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "execution_guard_binding_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "phase_u_outcome": phase_u_outcome,
                "required_phase_u_outcome": required_phase_u_outcome,
                "phase_u_authorized_lane_id": phase_u_authorized_lane_id,
                "required_phase_u_authorized_lane_id": required_phase_u_authorized_lane_id,
                "phase_u_packet_authorization": phase_u_packet_authorization,
                "required_phase_u_packet_authorization": required_phase_u_packet_authorization,
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
        "binding_closure": closure,
        "summary": {
            "terminal_outcome": terminal_outcome,
            "authorized_lane_id": required_phase_u_authorized_lane_id,
            "authorize_first_test_packet": authorize_first_test_packet,
            "next_action": next_action,
            "single_layer_only": bool(contract.get("single_layer_only", True)),
            "single_outcome_only": bool(contract.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_phase_u_execution_guard_authorization_ready_closure_report": _ptr(phase_u_path),
            "science_phase_o_authorized_candidate_next_step_selection_report": _ptr(phase_o_path),
            "science_closed_lane_non_reopen_reason_summary_report": _ptr(non_reopen_summary_path),
        },
        "non_claim_boundary": "Repository-local execution-guard binding closure report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate Phase V execution-guard binding closure report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "science_phase_v_execution_guard_binding_closure_20260412_v0.json",
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
        "science_phase_v_execution_guard_binding_closure_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']}"
        f" authorize_first_test_packet={payload['summary']['authorize_first_test_packet']}"
        f" out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
