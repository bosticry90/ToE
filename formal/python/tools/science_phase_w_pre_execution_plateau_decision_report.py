from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_PHASE_W_PRE_EXECUTION_PLATEAU_DECISION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_PHASE_W_PRE_EXECUTION_PLATEAU_DECISION_20260412_v0.json"
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
    contract = dict(declaration.get("plateau_decision_contract", {}))
    outcome_contract = dict(declaration.get("plateau_outcome_contract", {}))

    phase_v_path = REPO_ROOT / str(
        required_inputs.get("science_phase_v_execution_guard_binding_closure_report", "")
    ).strip()
    phase_s_path = REPO_ROOT / str(
        required_inputs.get("science_phase_s_authorization_readiness_closure_report", "")
    ).strip()
    non_reopen_summary_path = REPO_ROOT / str(
        required_inputs.get("science_closed_lane_non_reopen_reason_summary_report", "")
    ).strip()

    phase_v = _read_json(phase_v_path)
    phase_s = _read_json(phase_s_path)
    non_reopen_summary = _read_json(non_reopen_summary_path)

    phase_v_summary = dict(phase_v.get("summary", {}))
    phase_s_summary = dict(phase_s.get("summary", {}))

    phase_v_outcome = str(phase_v_summary.get("terminal_outcome", "")).strip()
    phase_v_authorized_lane_id = str(phase_v_summary.get("authorized_lane_id", "")).strip()
    phase_v_packet_authorization = bool(phase_v_summary.get("authorize_first_test_packet", True))
    phase_s_outcome = str(phase_s_summary.get("terminal_outcome", "")).strip()
    non_reopen_summary_outcome = str(
        dict(non_reopen_summary.get("summary", {})).get("terminal_outcome", "")
    ).strip()

    required_phase_v_outcome = str(contract.get("required_phase_v_outcome", "")).strip()
    required_phase_v_authorized_lane_id = str(contract.get("required_phase_v_authorized_lane_id", "")).strip()
    required_phase_v_packet_authorization = bool(contract.get("required_phase_v_packet_authorization", False))
    required_phase_s_outcome = str(contract.get("required_phase_s_outcome", "")).strip()
    required_non_reopen_summary_outcome = str(contract.get("required_non_reopen_summary_outcome", "")).strip()
    forbid_reopen = bool(contract.get("forbid_closed_or_held_lane_reopen", False))

    plateau_signals = dict(contract.get("plateau_signals", {}))
    authorization_state_changed_since_phase_s = bool(
        plateau_signals.get("authorization_state_changed_since_phase_s", False)
    )
    distinct_remaining_field_identified = bool(
        plateau_signals.get("distinct_remaining_field_identified", False)
    )
    residual_blocker_repetition_detected = bool(
        plateau_signals.get("residual_blocker_repetition_detected", False)
    )
    candidate_preservation_status_confirmed = bool(
        plateau_signals.get("candidate_preservation_status_confirmed", False)
    )
    policy_escalation_required = bool(plateau_signals.get("policy_escalation_required", False))

    signals_shape_ok = all(
        key in plateau_signals
        for key in [
            "authorization_state_changed_since_phase_s",
            "distinct_remaining_field_identified",
            "residual_blocker_repetition_detected",
            "candidate_preservation_status_confirmed",
            "policy_escalation_required",
        ]
    )

    preconditions_ok = (
        phase_v_outcome == required_phase_v_outcome
        and phase_v_authorized_lane_id == required_phase_v_authorized_lane_id
        and phase_v_packet_authorization == required_phase_v_packet_authorization
        and phase_s_outcome == required_phase_s_outcome
        and non_reopen_summary_outcome == required_non_reopen_summary_outcome
        and forbid_reopen
        and signals_shape_ok
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get("default_outcome", "PRE_EXECUTION_PLATEAU_DECISION_EVIDENCE_INCOMPLETE")
    ).strip()

    if not signals_shape_ok:
        terminal_outcome = "HOLD_PENDING_PRE_EXECUTION_PLATEAU_REPAIR"
        next_action = "REPAIR_PRE_EXECUTION_PLATEAU_SIGNAL_SHAPE"
    elif not preconditions_ok:
        terminal_outcome = "PRE_EXECUTION_PLATEAU_DECISION_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_PHASE_W_PRECONDITIONS_AND_RERUN"
    elif policy_escalation_required:
        terminal_outcome = "ESCALATE_TO_HIGHER_LEVEL_POLICY"
        next_action = "ESCALATE_TO_HIGHER_LEVEL_POLICY_FOR_PRE_EXECUTION_DECISION"
    elif not candidate_preservation_status_confirmed:
        terminal_outcome = "WITHDRAW_CANDIDATE_FROM_ACTIVE_PREPARATION"
        next_action = "WITHDRAW_CANDIDATE_AND_PRESERVE_HISTORY_ONLY"
    elif distinct_remaining_field_identified and not authorization_state_changed_since_phase_s:
        terminal_outcome = "AUTHORIZE_ONE_FINAL_CLOSURE_TRANCHE"
        next_action = "OPEN_ONE_FINAL_BOUNDED_CLOSURE_LAYER_FOR_NAMED_REMAINING_FIELD"
    elif residual_blocker_repetition_detected and not distinct_remaining_field_identified:
        terminal_outcome = "HOLD_CANDIDATE_AS_NEAR_READY_BUT_NOT_EXECUTABLE"
        next_action = "PRESERVE_NEAR_READY_STATUS_AND_STOP_FURTHER_CLOSURE_LOOP_UNTIL_NEW_FIELD_IS_IDENTIFIED"
    else:
        terminal_outcome = "AUTHORIZE_ONE_FINAL_CLOSURE_TRANCHE"
        next_action = "OPEN_ONE_FINAL_BOUNDED_CLOSURE_LAYER"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "phase_v_outcome_match": phase_v_outcome == required_phase_v_outcome,
            "phase_v_authorized_lane_id_match": phase_v_authorized_lane_id == required_phase_v_authorized_lane_id,
            "phase_v_packet_authorization_match": phase_v_packet_authorization == required_phase_v_packet_authorization,
            "phase_s_outcome_match": phase_s_outcome == required_phase_s_outcome,
            "non_reopen_summary_outcome_match": non_reopen_summary_outcome == required_non_reopen_summary_outcome,
            "forbid_closed_or_held_lane_reopen": forbid_reopen,
            "plateau_signal_shape_ok": signals_shape_ok,
            "single_terminal_outcome_rule_declared": str(
                outcome_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_W_PRE_EXECUTION_PLATEAU_DECISION_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_SCIENCE_PHASE_W_PRE_EXECUTION_PLATEAU_DECISION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "pre_execution_plateau_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "phase_v_outcome": phase_v_outcome,
                "required_phase_v_outcome": required_phase_v_outcome,
                "phase_v_authorized_lane_id": phase_v_authorized_lane_id,
                "required_phase_v_authorized_lane_id": required_phase_v_authorized_lane_id,
                "phase_v_packet_authorization": phase_v_packet_authorization,
                "required_phase_v_packet_authorization": required_phase_v_packet_authorization,
                "phase_s_outcome": phase_s_outcome,
                "required_phase_s_outcome": required_phase_s_outcome,
                "non_reopen_summary_outcome": non_reopen_summary_outcome,
                "required_non_reopen_summary_outcome": required_non_reopen_summary_outcome,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "plateau_signals": plateau_signals,
        "summary": {
            "terminal_outcome": terminal_outcome,
            "authorized_lane_id": required_phase_v_authorized_lane_id,
            "authorize_first_test_packet": False,
            "next_action": next_action,
            "single_layer_only": bool(contract.get("single_layer_only", True)),
            "single_outcome_only": bool(contract.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_phase_v_execution_guard_binding_closure_report": _ptr(phase_v_path),
            "science_phase_s_authorization_readiness_closure_report": _ptr(phase_s_path),
            "science_closed_lane_non_reopen_reason_summary_report": _ptr(non_reopen_summary_path),
        },
        "non_claim_boundary": "Repository-local pre-execution plateau decision report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate Phase W pre-execution plateau decision report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "science_phase_w_pre_execution_plateau_decision_20260412_v0.json",
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
        "science_phase_w_pre_execution_plateau_decision_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']}"
        f" out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
