from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_PHASE_F_UNTOUCHED_LANE_ATTACK_CLASS_RESELECTION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_PHASE_F_UNTOUCHED_LANE_ATTACK_CLASS_RESELECTION_20260412_v0.json"
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
    reselection_policy = dict(declaration.get("reselection_policy", {}))
    reselection_contract = dict(declaration.get("reselection_contract", {}))

    phase_d_selection_path = REPO_ROOT / str(
        required_inputs.get("science_phase_d_untouched_lane_selection_report", "")
    ).strip()
    first_test_path = REPO_ROOT / str(
        required_inputs.get("science_phase_d_untouched_lane_first_test_packet_report", "")
    ).strip()
    phase_e_decision_path = REPO_ROOT / str(
        required_inputs.get("science_phase_e_untouched_lane_post_first_test_decision_report", "")
    ).strip()
    non_reopen_summary_path = REPO_ROOT / str(
        required_inputs.get("science_closed_lane_non_reopen_reason_summary_report", "")
    ).strip()

    phase_d_selection = _read_json(phase_d_selection_path)
    first_test = _read_json(first_test_path)
    phase_e_decision = _read_json(phase_e_decision_path)
    non_reopen_summary = _read_json(non_reopen_summary_path)

    phase_d_selection_outcome = str(
        dict(phase_d_selection.get("summary", {})).get("terminal_outcome", "")
    ).strip()
    phase_d_selected_lane = str(
        dict(phase_d_selection.get("summary", {})).get("untouched_lane_candidate_id", "")
    ).strip()

    phase_d_first_test_outcome = str(
        dict(first_test.get("summary", {})).get("terminal_outcome", "")
    ).strip()
    previous_attack_class = str(
        dict(first_test.get("summary", {})).get("single_attack_class", "")
    ).strip()

    phase_e_decision_outcome = str(
        dict(phase_e_decision.get("summary", {})).get("terminal_outcome", "")
    ).strip()
    non_reopen_summary_outcome = str(
        dict(non_reopen_summary.get("summary", {})).get("terminal_outcome", "")
    ).strip()

    required_phase_d_selection_outcome = str(
        reselection_policy.get("required_phase_d_selection_outcome", "")
    ).strip()
    required_phase_d_first_test_outcome = str(
        reselection_policy.get("required_phase_d_first_test_outcome", "")
    ).strip()
    required_phase_e_decision_outcome = str(
        reselection_policy.get("required_phase_e_decision_outcome", "")
    ).strip()
    required_non_reopen_summary_outcome = str(
        reselection_policy.get("required_non_reopen_summary_outcome", "")
    ).strip()
    required_selected_untouched_lane = str(
        reselection_policy.get("required_selected_untouched_lane", "")
    ).strip()

    target_lane = str(reselection_policy.get("target_lane", "")).strip()
    declared_previous_attack_class = str(reselection_policy.get("previous_attack_class", "")).strip()

    signal_refinement_supported = bool(reselection_policy.get("signal_refinement_supported", False))
    interface_alignment_supported = bool(reselection_policy.get("interface_alignment_supported", False))
    different_target_subseam_supported = bool(
        reselection_policy.get("different_target_subseam_supported", False)
    )
    lane_underdefined_for_next_packet = bool(
        reselection_policy.get("lane_underdefined_for_next_packet", False)
    )

    preconditions_ok = (
        phase_d_selection_outcome == required_phase_d_selection_outcome
        and phase_d_first_test_outcome == required_phase_d_first_test_outcome
        and phase_e_decision_outcome == required_phase_e_decision_outcome
        and non_reopen_summary_outcome == required_non_reopen_summary_outcome
        and phase_d_selected_lane == required_selected_untouched_lane
        and phase_d_selected_lane == target_lane
        and previous_attack_class == declared_previous_attack_class
        and bool(previous_attack_class)
    )

    support_count = sum(
        [
            signal_refinement_supported,
            interface_alignment_supported,
            different_target_subseam_supported,
        ]
    )

    allowed_outcomes = set(reselection_contract.get("allowed_outcomes", []))
    default_outcome = str(reselection_contract.get("default_outcome", "HOLD_UNTOUCHED_LANE_AND_STOP")).strip()

    if not preconditions_ok:
        terminal_outcome = "HOLD_UNTOUCHED_LANE_AND_STOP"
        selected_next_attack_class = "NONE"
        next_action = "REPAIR_PHASE_F_PRECONDITIONS_AND_RERUN_RESELECTION"
    elif lane_underdefined_for_next_packet:
        terminal_outcome = "HOLD_UNTOUCHED_LANE_AND_STOP"
        selected_next_attack_class = "NONE"
        next_action = "STOP_AND_REQUIRE_LANE_SPECIFICATION_BEFORE_NEXT_PACKET"
    elif support_count != 1:
        terminal_outcome = "HOLD_UNTOUCHED_LANE_AND_STOP"
        selected_next_attack_class = "NONE"
        next_action = "REPAIR_RESELECTION_SUPPORT_VECTOR_TO_ONE_CLASS"
    elif interface_alignment_supported:
        terminal_outcome = "UNTOUCHED_LANE_INTERFACE_ALIGNMENT_ATTACK"
        selected_next_attack_class = "neutrino_interface_alignment_boundary_probe"
        next_action = "OPEN_ONE_BOUNDED_PACKET_UNDER_SELECTED_ATTACK_CLASS"
    elif signal_refinement_supported:
        terminal_outcome = "UNTOUCHED_LANE_SIGNAL_REFINEMENT_ATTACK"
        selected_next_attack_class = "neutrino_signal_refinement_local_probe"
        next_action = "OPEN_ONE_BOUNDED_PACKET_UNDER_SELECTED_ATTACK_CLASS"
    elif different_target_subseam_supported:
        terminal_outcome = "UNTOUCHED_LANE_DIFFERENT_TARGET_SUBSEAM_ATTACK"
        selected_next_attack_class = "neutrino_target_subseam_bridge_probe"
        next_action = "OPEN_ONE_BOUNDED_PACKET_UNDER_SELECTED_ATTACK_CLASS"
    else:
        terminal_outcome = "HOLD_UNTOUCHED_LANE_AND_STOP"
        selected_next_attack_class = "NONE"
        next_action = "STOP_AND_REQUIRE_RESELECTION_REPAIR"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "phase_d_selection_outcome_match": phase_d_selection_outcome == required_phase_d_selection_outcome,
            "phase_d_first_test_outcome_match": phase_d_first_test_outcome == required_phase_d_first_test_outcome,
            "phase_e_decision_outcome_match": phase_e_decision_outcome == required_phase_e_decision_outcome,
            "non_reopen_summary_outcome_match": non_reopen_summary_outcome == required_non_reopen_summary_outcome,
            "selected_lane_match": phase_d_selected_lane == required_selected_untouched_lane,
            "selected_lane_matches_target": phase_d_selected_lane == target_lane,
            "previous_attack_class_match": previous_attack_class == declared_previous_attack_class,
            "single_support_class_selected": support_count == 1,
            "single_terminal_outcome_rule_declared": str(
                reselection_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_F_UNTOUCHED_LANE_ATTACK_CLASS_RESELECTION_OUTCOME",
            "no_loop_rule_declared": str(reselection_contract.get("no_loop_rule", "")).strip()
            == "ONE_SCIENCE_PHASE_F_UNTOUCHED_LANE_ATTACK_CLASS_RESELECTION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "reselection_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "phase_d_selection_outcome": phase_d_selection_outcome,
                "required_phase_d_selection_outcome": required_phase_d_selection_outcome,
                "phase_d_first_test_outcome": phase_d_first_test_outcome,
                "required_phase_d_first_test_outcome": required_phase_d_first_test_outcome,
                "phase_e_decision_outcome": phase_e_decision_outcome,
                "required_phase_e_decision_outcome": required_phase_e_decision_outcome,
                "non_reopen_summary_outcome": non_reopen_summary_outcome,
                "required_non_reopen_summary_outcome": required_non_reopen_summary_outcome,
                "selected_lane": phase_d_selected_lane,
                "required_selected_untouched_lane": required_selected_untouched_lane,
                "target_lane": target_lane,
                "previous_attack_class": previous_attack_class,
                "declared_previous_attack_class": declared_previous_attack_class,
                "signal_refinement_supported": signal_refinement_supported,
                "interface_alignment_supported": interface_alignment_supported,
                "different_target_subseam_supported": different_target_subseam_supported,
                "lane_underdefined_for_next_packet": lane_underdefined_for_next_packet,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "target_lane": target_lane,
            "previous_attack_class": previous_attack_class,
            "selected_next_attack_class": selected_next_attack_class,
            "next_action": next_action,
            "single_layer_only": bool(reselection_policy.get("single_layer_only", True)),
            "single_outcome_only": bool(reselection_policy.get("single_outcome_only", True)),
            "continue_authorized": terminal_outcome
            in {
                "UNTOUCHED_LANE_SIGNAL_REFINEMENT_ATTACK",
                "UNTOUCHED_LANE_INTERFACE_ALIGNMENT_ATTACK",
                "UNTOUCHED_LANE_DIFFERENT_TARGET_SUBSEAM_ATTACK",
            },
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_phase_d_untouched_lane_selection_report": _ptr(phase_d_selection_path),
            "science_phase_d_untouched_lane_first_test_packet_report": _ptr(first_test_path),
            "science_phase_e_untouched_lane_post_first_test_decision_report": _ptr(phase_e_decision_path),
            "science_closed_lane_non_reopen_reason_summary_report": _ptr(non_reopen_summary_path),
        },
        "non_claim_boundary": "Repository-local untouched-lane attack-class reselection report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate Phase F untouched-lane attack-class reselection report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "science_phase_f_untouched_lane_attack_class_reselection_20260412_v0.json",
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
        "science_phase_f_untouched_lane_attack_class_reselection_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']}"
        f" selected_next_attack_class={payload['summary']['selected_next_attack_class']}"
        f" out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
