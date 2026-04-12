from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_PHASE_Z_STRONGER_CANDIDATE_CLASS_DISCOVERY_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_PHASE_Z_STRONGER_CANDIDATE_CLASS_DISCOVERY_20260412_v0.json"
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
    contract = dict(declaration.get("stronger_candidate_class_discovery_contract", {}))
    outcome_contract = dict(declaration.get("stronger_candidate_class_discovery_outcome_contract", {}))

    phase_y_path = REPO_ROOT / str(
        required_inputs.get("science_phase_y_post_comparative_synthesis_decision_report", "")
    ).strip()
    phase_x_path = REPO_ROOT / str(
        required_inputs.get("science_phase_x_governed_lane_end_comparative_synthesis_report", "")
    ).strip()
    non_reopen_summary_path = REPO_ROOT / str(
        required_inputs.get("science_closed_lane_non_reopen_reason_summary_report", "")
    ).strip()

    phase_y = _read_json(phase_y_path)
    phase_x = _read_json(phase_x_path)
    non_reopen_summary = _read_json(non_reopen_summary_path)

    phase_y_summary = dict(phase_y.get("summary", {}))
    phase_x_summary = dict(phase_x.get("summary", {}))

    phase_y_outcome = str(phase_y_summary.get("terminal_outcome", "")).strip()
    phase_x_outcome = str(phase_x_summary.get("terminal_outcome", "")).strip()
    non_reopen_summary_outcome = str(
        dict(non_reopen_summary.get("summary", {})).get("terminal_outcome", "")
    ).strip()
    thermal_lane_status = str(phase_x_summary.get("thermal_boundary_lane_status", "")).strip()
    thermal_no_further_closure_authorized = bool(
        phase_x_summary.get("thermal_boundary_no_further_closure_authorized", True)
    )
    thermal_packet_authorized = bool(phase_x_summary.get("thermal_boundary_packet_authorized", True))

    required_phase_y_outcome = str(contract.get("required_phase_y_outcome", "")).strip()
    required_phase_x_outcome = str(contract.get("required_phase_x_outcome", "")).strip()
    required_non_reopen_summary_outcome = str(
        contract.get("required_non_reopen_summary_outcome", "")
    ).strip()
    required_thermal_lane_status = str(contract.get("required_thermal_lane_status", "")).strip()
    required_thermal_no_further_closure_authorized = bool(
        contract.get("required_thermal_no_further_closure_authorized", True)
    )
    required_thermal_packet_authorized = bool(contract.get("required_thermal_packet_authorized", False))

    forbid_reopen = bool(contract.get("forbid_closed_or_held_lane_reopen", False))

    signals = dict(contract.get("discovery_signals", {}))
    candidate_class_structural_properties_defined = bool(
        signals.get("candidate_class_structural_properties_defined", False)
    )
    candidate_class_observable_interface_requirements_defined = bool(
        signals.get("candidate_class_observable_interface_requirements_defined", False)
    )
    candidate_class_exclusion_patterns_defined = bool(
        signals.get("candidate_class_exclusion_patterns_defined", False)
    )
    stronger_candidate_class_named = bool(signals.get("stronger_candidate_class_named", False))
    higher_level_policy_revision_needed = bool(signals.get("higher_level_policy_revision_needed", False))
    maintain_governed_stop_state = bool(signals.get("maintain_governed_stop_state", False))

    signals_shape_ok = all(
        key in signals
        for key in [
            "candidate_class_structural_properties_defined",
            "candidate_class_observable_interface_requirements_defined",
            "candidate_class_exclusion_patterns_defined",
            "stronger_candidate_class_named",
            "higher_level_policy_revision_needed",
            "maintain_governed_stop_state",
        ]
    )

    preconditions_ok = (
        phase_y_outcome == required_phase_y_outcome
        and phase_x_outcome == required_phase_x_outcome
        and non_reopen_summary_outcome == required_non_reopen_summary_outcome
        and thermal_lane_status == required_thermal_lane_status
        and thermal_no_further_closure_authorized == required_thermal_no_further_closure_authorized
        and thermal_packet_authorized == required_thermal_packet_authorized
        and forbid_reopen
        and signals_shape_ok
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get("default_outcome", "STRONGER_CANDIDATE_CLASS_DISCOVERY_EVIDENCE_INCOMPLETE")
    ).strip()

    if not signals_shape_ok:
        terminal_outcome = "HOLD_PENDING_STRONGER_CANDIDATE_CLASS_DISCOVERY_REPAIR"
        next_action = "REPAIR_STRONGER_CANDIDATE_CLASS_DISCOVERY_SIGNAL_SHAPE"
    elif not preconditions_ok:
        terminal_outcome = "STRONGER_CANDIDATE_CLASS_DISCOVERY_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_PHASE_Z_PRECONDITIONS_AND_RERUN"
    elif stronger_candidate_class_named:
        terminal_outcome = "STRONGER_CANDIDATE_CLASS_IDENTIFIED"
        next_action = "OPEN_ONE_BOUNDED_FUTURE_LANE_SCREEN_FOR_THE_NAMED_STRONGER_CLASS"
    elif higher_level_policy_revision_needed:
        terminal_outcome = "REQUIRES_HIGHER_LEVEL_POLICY_REVISION"
        next_action = "OPEN_ONE_BOUNDED_HIGHER_LEVEL_POLICY_REVISION_LAYER"
    elif maintain_governed_stop_state:
        terminal_outcome = "MAINTAIN_CURRENT_GOVERNED_STOP_STATE"
        next_action = "MAINTAIN_CURRENT_GOVERNED_STOP_STATE_UNTIL_NEW_EVIDENCE_CLASS_APPEARS"
    elif (
        candidate_class_structural_properties_defined
        and candidate_class_observable_interface_requirements_defined
        and candidate_class_exclusion_patterns_defined
    ):
        terminal_outcome = "NO_STRONGER_CANDIDATE_CLASS_IDENTIFIED_YET"
        next_action = "WAIT_FOR_STRONGER_CANDIDATE_CLASS_AND_KEEP_ALL_CURRENT_LANES_CLOSED_OR_HELD"
    else:
        terminal_outcome = "STRONGER_CANDIDATE_CLASS_DISCOVERY_EVIDENCE_INCOMPLETE"
        next_action = "COMPLETE_MISSING_STRONGER_CANDIDATE_CLASS_DISCOVERY_SIGNALS"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    stronger_candidate_discovery_framework = {
        "required_structural_properties": [
            "must_reduce_repetition_of_partial_hold_patterns_observed_in_near_ready_but_not_executable_lanes",
            "must_provide_distinct_remaining_field_not_already_exhausted_by_current_candidate_family",
            "must_keep_execution_packet_authorization_separate_from_discovery_and_screening_layers"
        ],
        "required_observable_interface_features": [
            "explicit_external_comparator_binding_path_or_clear_probe_readiness_bridge",
            "declared_interface_regime_with_non_aliasing_to_closed_or_held_lane_families",
            "bounded falsification_or_discriminative_signal_surface_defined_before_screening"
        ],
        "excluded_candidate_patterns": [
            "candidate_families_that_reproduce_valid_but_nonmoving_without_new_structure",
            "candidate_families_that_reproduce_near_ready_but_not_executable_without_new_remaining_field",
            "candidate_families_that_require_reopen_of_closed_or_held_lanes"
        ]
    }

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "phase_y_outcome_match": phase_y_outcome == required_phase_y_outcome,
            "phase_x_outcome_match": phase_x_outcome == required_phase_x_outcome,
            "non_reopen_summary_outcome_match": non_reopen_summary_outcome
            == required_non_reopen_summary_outcome,
            "thermal_lane_status_match": thermal_lane_status == required_thermal_lane_status,
            "thermal_no_further_closure_authorized_match": thermal_no_further_closure_authorized
            == required_thermal_no_further_closure_authorized,
            "thermal_packet_authorized_match": thermal_packet_authorized
            == required_thermal_packet_authorized,
            "forbid_closed_or_held_lane_reopen": forbid_reopen,
            "discovery_signal_shape_ok": signals_shape_ok,
            "single_terminal_outcome_rule_declared": str(
                outcome_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_Z_STRONGER_CANDIDATE_CLASS_DISCOVERY_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_SCIENCE_PHASE_Z_STRONGER_CANDIDATE_CLASS_DISCOVERY_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "stronger_candidate_class_discovery_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "phase_y_outcome": phase_y_outcome,
                "required_phase_y_outcome": required_phase_y_outcome,
                "phase_x_outcome": phase_x_outcome,
                "required_phase_x_outcome": required_phase_x_outcome,
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
        "discovery_signals": signals,
        "stronger_candidate_discovery_framework": stronger_candidate_discovery_framework,
        "summary": {
            "terminal_outcome": terminal_outcome,
            "thermal_boundary_lane_status": thermal_lane_status,
            "thermal_boundary_no_further_closure_authorized": thermal_no_further_closure_authorized,
            "thermal_boundary_packet_authorized": thermal_packet_authorized,
            "lane_specific_reopen_authorized": False,
            "single_layer_only": bool(contract.get("single_layer_only", True)),
            "single_outcome_only": bool(contract.get("single_outcome_only", True)),
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_phase_y_post_comparative_synthesis_decision_report": _ptr(phase_y_path),
            "science_phase_x_governed_lane_end_comparative_synthesis_report": _ptr(phase_x_path),
            "science_closed_lane_non_reopen_reason_summary_report": _ptr(non_reopen_summary_path),
        },
        "non_claim_boundary": "Repository-local stronger-candidate-class discovery report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate Phase Z stronger-candidate-class discovery report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "science_phase_z_stronger_candidate_class_discovery_20260412_v0.json",
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
        "science_phase_z_stronger_candidate_class_discovery_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']}"
        f" out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
