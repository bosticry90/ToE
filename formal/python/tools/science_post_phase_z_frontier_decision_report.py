from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_POST_PHASE_Z_FRONTIER_DECISION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_POST_PHASE_Z_FRONTIER_DECISION_20260412_v0.json"
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
    contract = dict(declaration.get("post_phase_z_frontier_decision_contract", {}))
    outcome_contract = dict(declaration.get("post_phase_z_frontier_decision_outcome_contract", {}))

    phase_z_path = REPO_ROOT / str(
        required_inputs.get("science_phase_z_stronger_candidate_class_discovery_report", "")
    ).strip()
    phase_y_path = REPO_ROOT / str(
        required_inputs.get("science_phase_y_post_comparative_synthesis_decision_report", "")
    ).strip()
    non_reopen_summary_path = REPO_ROOT / str(
        required_inputs.get("science_closed_lane_non_reopen_reason_summary_report", "")
    ).strip()

    phase_z = _read_json(phase_z_path)
    phase_y = _read_json(phase_y_path)
    non_reopen_summary = _read_json(non_reopen_summary_path)

    phase_z_summary = dict(phase_z.get("summary", {}))
    phase_y_summary = dict(phase_y.get("summary", {}))

    phase_z_outcome = str(phase_z_summary.get("terminal_outcome", "")).strip()
    phase_y_outcome = str(phase_y_summary.get("terminal_outcome", "")).strip()
    non_reopen_summary_outcome = str(
        dict(non_reopen_summary.get("summary", {})).get("terminal_outcome", "")
    ).strip()

    thermal_lane_status = str(phase_z_summary.get("thermal_boundary_lane_status", "")).strip()
    thermal_no_further_closure_authorized = bool(
        phase_z_summary.get("thermal_boundary_no_further_closure_authorized", True)
    )
    thermal_packet_authorized = bool(phase_z_summary.get("thermal_boundary_packet_authorized", True))

    required_phase_z_outcome = str(contract.get("required_phase_z_outcome", "")).strip()
    required_phase_y_outcome = str(contract.get("required_phase_y_outcome", "")).strip()
    required_non_reopen_summary_outcome = str(
        contract.get("required_non_reopen_summary_outcome", "")
    ).strip()
    required_thermal_lane_status = str(contract.get("required_thermal_lane_status", "")).strip()
    required_thermal_no_further_closure_authorized = bool(
        contract.get("required_thermal_no_further_closure_authorized", True)
    )
    required_thermal_packet_authorized = bool(contract.get("required_thermal_packet_authorized", False))

    forbid_reopen = bool(contract.get("forbid_closed_or_held_lane_reopen", False))

    frontier_signals = dict(contract.get("frontier_signals", {}))
    preserve_current_governed_stop_state = bool(
        frontier_signals.get("preserve_current_governed_stop_state", False)
    )
    revise_higher_level_policy = bool(frontier_signals.get("revise_higher_level_policy", False))
    open_candidate_generation_framework_redesign = bool(
        frontier_signals.get("open_candidate_generation_framework_redesign", False)
    )
    wait_for_external_evidence_inputs = bool(
        frontier_signals.get("wait_for_external_evidence_inputs", False)
    )
    force_policy_escalation_now = bool(frontier_signals.get("force_policy_escalation_now", False))

    signals_shape_ok = all(
        key in frontier_signals
        for key in [
            "preserve_current_governed_stop_state",
            "revise_higher_level_policy",
            "open_candidate_generation_framework_redesign",
            "wait_for_external_evidence_inputs",
            "force_policy_escalation_now",
        ]
    )

    selected_signal_count = sum(
        1
        for value in [
            preserve_current_governed_stop_state,
            revise_higher_level_policy,
            open_candidate_generation_framework_redesign,
            wait_for_external_evidence_inputs,
        ]
        if value
    )

    preconditions_ok = (
        phase_z_outcome == required_phase_z_outcome
        and phase_y_outcome == required_phase_y_outcome
        and non_reopen_summary_outcome == required_non_reopen_summary_outcome
        and thermal_lane_status == required_thermal_lane_status
        and thermal_no_further_closure_authorized == required_thermal_no_further_closure_authorized
        and thermal_packet_authorized == required_thermal_packet_authorized
        and forbid_reopen
        and signals_shape_ok
        and selected_signal_count <= 1
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get("default_outcome", "POST_PHASE_Z_FRONTIER_DECISION_EVIDENCE_INCOMPLETE")
    ).strip()

    if not signals_shape_ok:
        terminal_outcome = "HOLD_PENDING_POST_PHASE_Z_FRONTIER_DECISION_REPAIR"
        next_action = "REPAIR_POST_PHASE_Z_FRONTIER_DECISION_SIGNAL_SHAPE"
    elif not preconditions_ok:
        terminal_outcome = "POST_PHASE_Z_FRONTIER_DECISION_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_POST_PHASE_Z_FRONTIER_DECISION_PRECONDITIONS_AND_RERUN"
    elif force_policy_escalation_now or revise_higher_level_policy:
        terminal_outcome = "REVISE_HIGHER_LEVEL_POLICY"
        next_action = "OPEN_ONE_BOUNDED_HIGHER_LEVEL_POLICY_REVISION_LAYER"
    elif open_candidate_generation_framework_redesign:
        terminal_outcome = "OPEN_CANDIDATE_GENERATION_FRAMEWORK_REDESIGN"
        next_action = "OPEN_ONE_BOUNDED_CANDIDATE_GENERATION_FRAMEWORK_REDESIGN_LAYER"
    elif wait_for_external_evidence_inputs:
        terminal_outcome = "WAIT_FOR_EXTERNAL_EVIDENCE_INPUTS"
        next_action = "PRESERVE_STOP_STATE_UNTIL_EXTERNAL_EVIDENCE_OR_INPUTS_CHANGE"
    else:
        terminal_outcome = "PRESERVE_CURRENT_GOVERNED_STOP_STATE"
        next_action = "PRESERVE_CANONICAL_GOVERNED_STOP_STATE_UNTIL_GENUINELY_NEW_INPUT_CLASS"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "phase_z_outcome_match": phase_z_outcome == required_phase_z_outcome,
            "phase_y_outcome_match": phase_y_outcome == required_phase_y_outcome,
            "non_reopen_summary_outcome_match": non_reopen_summary_outcome
            == required_non_reopen_summary_outcome,
            "thermal_lane_status_match": thermal_lane_status == required_thermal_lane_status,
            "thermal_no_further_closure_authorized_match": thermal_no_further_closure_authorized
            == required_thermal_no_further_closure_authorized,
            "thermal_packet_authorized_match": thermal_packet_authorized
            == required_thermal_packet_authorized,
            "forbid_closed_or_held_lane_reopen": forbid_reopen,
            "frontier_signal_shape_ok": signals_shape_ok,
            "single_frontier_signal_selected": selected_signal_count <= 1,
            "single_terminal_outcome_rule_declared": str(
                outcome_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SCIENCE_POST_PHASE_Z_FRONTIER_DECISION_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_SCIENCE_POST_PHASE_Z_FRONTIER_DECISION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "post_phase_z_frontier_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "phase_z_outcome": phase_z_outcome,
                "required_phase_z_outcome": required_phase_z_outcome,
                "phase_y_outcome": phase_y_outcome,
                "required_phase_y_outcome": required_phase_y_outcome,
                "non_reopen_summary_outcome": non_reopen_summary_outcome,
                "required_non_reopen_summary_outcome": required_non_reopen_summary_outcome,
                "thermal_lane_status": thermal_lane_status,
                "required_thermal_lane_status": required_thermal_lane_status,
                "thermal_no_further_closure_authorized": thermal_no_further_closure_authorized,
                "required_thermal_no_further_closure_authorized": required_thermal_no_further_closure_authorized,
                "thermal_packet_authorized": thermal_packet_authorized,
                "required_thermal_packet_authorized": required_thermal_packet_authorized,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "frontier_signals": frontier_signals,
        "summary": {
            "terminal_outcome": terminal_outcome,
            "thermal_boundary_lane_status": thermal_lane_status,
            "thermal_boundary_no_further_closure_authorized": thermal_no_further_closure_authorized,
            "thermal_boundary_packet_authorized": thermal_packet_authorized,
            "lane_specific_reopen_authorized": False,
            "new_lane_or_packet_authorized_now": False,
            "single_layer_only": bool(contract.get("single_layer_only", True)),
            "single_outcome_only": bool(contract.get("single_outcome_only", True)),
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_phase_z_stronger_candidate_class_discovery_report": _ptr(phase_z_path),
            "science_phase_y_post_comparative_synthesis_decision_report": _ptr(phase_y_path),
            "science_closed_lane_non_reopen_reason_summary_report": _ptr(non_reopen_summary_path),
        },
        "non_claim_boundary": "Repository-local post-Phase-Z frontier decision report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate post-Phase-Z frontier decision report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "science_post_phase_z_frontier_decision_20260412_v0.json",
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
        "science_post_phase_z_frontier_decision_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']}"
        f" out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
