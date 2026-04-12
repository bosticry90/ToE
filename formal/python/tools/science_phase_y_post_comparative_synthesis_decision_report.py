from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_PHASE_Y_POST_COMPARATIVE_SYNTHESIS_DECISION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_PHASE_Y_POST_COMPARATIVE_SYNTHESIS_DECISION_20260412_v0.json"
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
    contract = dict(declaration.get("post_comparative_decision_contract", {}))
    outcome_contract = dict(declaration.get("post_comparative_decision_outcome_contract", {}))

    phase_x_path = REPO_ROOT / str(
        required_inputs.get("science_phase_x_governed_lane_end_comparative_synthesis_report", "")
    ).strip()
    phase_w_path = REPO_ROOT / str(
        required_inputs.get("science_phase_w_pre_execution_plateau_decision_report", "")
    ).strip()
    non_reopen_summary_path = REPO_ROOT / str(
        required_inputs.get("science_closed_lane_non_reopen_reason_summary_report", "")
    ).strip()

    phase_x = _read_json(phase_x_path)
    phase_w = _read_json(phase_w_path)
    non_reopen_summary = _read_json(non_reopen_summary_path)

    phase_x_summary = dict(phase_x.get("summary", {}))
    phase_w_summary = dict(phase_w.get("summary", {}))
    phase_x_lane_states = dict(phase_x.get("governed_lane_end_states", {}))

    required_phase_x_outcome = str(contract.get("required_phase_x_outcome", "")).strip()
    required_thermal_lane_id = str(contract.get("required_thermal_lane_id", "")).strip()
    required_thermal_lane_status = str(contract.get("required_thermal_lane_status", "")).strip()
    required_thermal_no_further_closure_authorized = bool(
        contract.get("required_thermal_no_further_closure_authorized", False)
    )
    required_thermal_packet_authorized = bool(contract.get("required_thermal_packet_authorized", False))
    required_phase_w_outcome = str(contract.get("required_phase_w_outcome", "")).strip()
    required_non_reopen_summary_outcome = str(
        contract.get("required_non_reopen_summary_outcome", "")
    ).strip()

    phase_x_outcome = str(phase_x_summary.get("terminal_outcome", "")).strip()
    phase_x_thermal_lane_status = str(phase_x_summary.get("thermal_boundary_lane_status", "")).strip()
    phase_x_thermal_no_further_closure_authorized = bool(
        phase_x_summary.get("thermal_boundary_no_further_closure_authorized", True)
    )
    phase_x_thermal_packet_authorized = bool(phase_x_summary.get("thermal_boundary_packet_authorized", True))

    phase_w_outcome = str(phase_w_summary.get("terminal_outcome", "")).strip()
    non_reopen_summary_outcome = str(
        dict(non_reopen_summary.get("summary", {})).get("terminal_outcome", "")
    ).strip()

    thermal_lane_state = dict(phase_x_lane_states.get(required_thermal_lane_id, {}))
    thermal_lane_state_classification = str(thermal_lane_state.get("classification", "")).strip()

    forbid_reopen = bool(contract.get("forbid_closed_or_held_lane_reopen", False))

    decision_signals = dict(contract.get("decision_signals", {}))
    revise_higher_level_policy_for_near_ready_lanes = bool(
        decision_signals.get("revise_higher_level_policy_for_near_ready_lanes", False)
    )
    wait_for_stronger_candidate_class = bool(
        decision_signals.get("wait_for_stronger_candidate_class", False)
    )
    open_new_meta_selection_lane = bool(decision_signals.get("open_new_meta_selection_lane", False))
    maintain_current_governed_stop_state = bool(
        decision_signals.get("maintain_current_governed_stop_state", False)
    )
    force_policy_decision_escalation_now = bool(
        decision_signals.get("force_policy_decision_escalation_now", False)
    )

    decision_signal_shape_ok = all(
        key in decision_signals
        for key in [
            "revise_higher_level_policy_for_near_ready_lanes",
            "wait_for_stronger_candidate_class",
            "open_new_meta_selection_lane",
            "maintain_current_governed_stop_state",
            "force_policy_decision_escalation_now",
        ]
    )

    selected_signal_count = sum(
        1
        for value in [
            revise_higher_level_policy_for_near_ready_lanes,
            wait_for_stronger_candidate_class,
            open_new_meta_selection_lane,
            maintain_current_governed_stop_state,
        ]
        if value
    )

    preconditions_ok = (
        phase_x_outcome == required_phase_x_outcome
        and phase_x_thermal_lane_status == required_thermal_lane_status
        and thermal_lane_state_classification == "NEAR_READY_BUT_NOT_EXECUTABLE_PRESERVED_INACTIVE"
        and phase_x_thermal_no_further_closure_authorized == required_thermal_no_further_closure_authorized
        and phase_x_thermal_packet_authorized == required_thermal_packet_authorized
        and phase_w_outcome == required_phase_w_outcome
        and non_reopen_summary_outcome == required_non_reopen_summary_outcome
        and forbid_reopen
        and decision_signal_shape_ok
        and selected_signal_count <= 1
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get("default_outcome", "POST_COMPARATIVE_DECISION_EVIDENCE_INCOMPLETE")
    ).strip()

    if not decision_signal_shape_ok:
        terminal_outcome = "HOLD_PENDING_POST_COMPARATIVE_DECISION_REPAIR"
        next_action = "REPAIR_POST_COMPARATIVE_DECISION_SIGNAL_SHAPE"
    elif not preconditions_ok:
        terminal_outcome = "POST_COMPARATIVE_DECISION_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_PHASE_Y_PRECONDITIONS_AND_RERUN"
    elif force_policy_decision_escalation_now or revise_higher_level_policy_for_near_ready_lanes:
        terminal_outcome = "REVISE_HIGHER_LEVEL_POLICY_FOR_NEAR_READY_LANES"
        next_action = "OPEN_ONE_BOUNDED_HIGHER_LEVEL_POLICY_REVISION_LAYER"
    elif open_new_meta_selection_lane:
        terminal_outcome = "OPEN_NEW_META_SELECTION_LANE"
        next_action = "OPEN_ONE_BOUNDED_META_SELECTION_LANE_WITH_NO_CLOSED_LANE_REOPEN"
    elif maintain_current_governed_stop_state:
        terminal_outcome = "MAINTAIN_CURRENT_GOVERNED_STOP_STATE"
        next_action = "MAINTAIN_STOP_STATE_AND_REEVALUATE_ONLY_ON_NEW_EVIDENCE_CLASS"
    else:
        terminal_outcome = "WAIT_FOR_STRONGER_CANDIDATE_CLASS"
        next_action = "WAIT_FOR_STRONGER_CANDIDATE_CLASS_BEFORE_NEW_MATURATION_PROGRAM"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "phase_x_outcome_match": phase_x_outcome == required_phase_x_outcome,
            "thermal_lane_status_match": phase_x_thermal_lane_status == required_thermal_lane_status,
            "thermal_lane_classification_match": thermal_lane_state_classification
            == "NEAR_READY_BUT_NOT_EXECUTABLE_PRESERVED_INACTIVE",
            "thermal_no_further_closure_authorized_match": phase_x_thermal_no_further_closure_authorized
            == required_thermal_no_further_closure_authorized,
            "thermal_packet_authorized_match": phase_x_thermal_packet_authorized
            == required_thermal_packet_authorized,
            "phase_w_outcome_match": phase_w_outcome == required_phase_w_outcome,
            "non_reopen_summary_outcome_match": non_reopen_summary_outcome
            == required_non_reopen_summary_outcome,
            "forbid_closed_or_held_lane_reopen": forbid_reopen,
            "decision_signal_shape_ok": decision_signal_shape_ok,
            "single_decision_signal_selected": selected_signal_count <= 1,
            "single_terminal_outcome_rule_declared": str(
                outcome_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_Y_POST_COMPARATIVE_SYNTHESIS_DECISION_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_SCIENCE_PHASE_Y_POST_COMPARATIVE_SYNTHESIS_DECISION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "post_comparative_decision_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "phase_x_outcome": phase_x_outcome,
                "required_phase_x_outcome": required_phase_x_outcome,
                "phase_x_thermal_lane_status": phase_x_thermal_lane_status,
                "required_thermal_lane_status": required_thermal_lane_status,
                "phase_x_thermal_no_further_closure_authorized": phase_x_thermal_no_further_closure_authorized,
                "required_thermal_no_further_closure_authorized": required_thermal_no_further_closure_authorized,
                "phase_x_thermal_packet_authorized": phase_x_thermal_packet_authorized,
                "required_thermal_packet_authorized": required_thermal_packet_authorized,
                "phase_w_outcome": phase_w_outcome,
                "required_phase_w_outcome": required_phase_w_outcome,
                "non_reopen_summary_outcome": non_reopen_summary_outcome,
                "required_non_reopen_summary_outcome": required_non_reopen_summary_outcome,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "decision_signals": decision_signals,
        "summary": {
            "terminal_outcome": terminal_outcome,
            "thermal_boundary_lane_status": phase_x_thermal_lane_status,
            "thermal_boundary_no_further_closure_authorized": phase_x_thermal_no_further_closure_authorized,
            "thermal_boundary_packet_authorized": phase_x_thermal_packet_authorized,
            "lane_specific_reopen_authorized": False,
            "single_layer_only": bool(contract.get("single_layer_only", True)),
            "single_outcome_only": bool(contract.get("single_outcome_only", True)),
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_phase_x_governed_lane_end_comparative_synthesis_report": _ptr(phase_x_path),
            "science_phase_w_pre_execution_plateau_decision_report": _ptr(phase_w_path),
            "science_closed_lane_non_reopen_reason_summary_report": _ptr(non_reopen_summary_path),
        },
        "non_claim_boundary": "Repository-local post-comparative project decision report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate Phase Y post-comparative synthesis decision report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "science_phase_y_post_comparative_synthesis_decision_20260412_v0.json",
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
        "science_phase_y_post_comparative_synthesis_decision_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']}"
        f" out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
