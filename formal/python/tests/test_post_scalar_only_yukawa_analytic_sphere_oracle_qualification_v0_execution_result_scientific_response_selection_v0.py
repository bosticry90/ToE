from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.tools import (
    post_scalar_only_yukawa_analytic_sphere_oracle_qualification_v0_execution_result_scientific_response_selection_v0
    as selection,
)


ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = ROOT / selection.REPORT_RELATIVE_PATH


def _report() -> dict[str, Any]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_selector_regenerates_and_freezes_accepted_review_authority() -> None:
    assert selection.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == selection.TARGET
    assert report["verdict"] == selection.VERDICT
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_result_review_artifacts"]
    } == selection.AUTHORITY_HASHES
    for relative_path, expected in selection.AUTHORITY_HASHES.items():
        assert _sha256(ROOT / relative_path) == expected


def test_bounded_production_comparison_is_unique_baseline_winner() -> None:
    ranking = _report()["ranking"]
    assert ranking["selected_candidate_id"] == selection.SELECTED_CANDIDATE_ID
    assert ranking["selected_score"] == 220
    assert ranking["runner_up_candidate_id"] == "DIRECT_ANALYTIC_KERNEL_REPLACEMENT"
    assert ranking["runner_up_score"] == 160
    assert ranking["winning_margin"] == 60
    assert len(ranking["rows"]) == 6


def test_all_six_routes_are_explicitly_ranked() -> None:
    identifiers = {row["candidate_id"] for row in _report()["ranking"]["rows"]}
    assert identifiers == {
        selection.SELECTED_CANDIDATE_ID,
        "DIRECT_ANALYTIC_KERNEL_REPLACEMENT",
        "DIRECT_TORQUE_AND_DFT_VALIDATION",
        "APPARATUS_REDESIGN",
        "CLOSE_SYNTHETIC_TORSION_BALANCE_LANE",
        "PIVOT_TO_NATIVE_GRAVITY_PRIORITY",
    }


def test_selection_is_stable_in_all_thirty_sensitivity_variants() -> None:
    sensitivity = _report()["sensitivity_analysis"]
    assert sensitivity["variant_count"] == 30
    assert sensitivity["selected_candidate_stable_in_all_variants"] is True
    assert sensitivity["minimum_winning_margin"] == 45
    assert all(
        row["selected_candidate_id"] == selection.SELECTED_CANDIDATE_ID
        for row in sensitivity["rows"]
    )


def test_case_grid_replays_failures_and_remains_small() -> None:
    grid = _report()["comparison_packet_preparation_requirements"]["case_grid"]
    assert grid["minimum_case_count"] == 6
    assert grid["maximum_case_count"] == 8
    assert grid["three_failed_stage_a_cases_required"] is True
    assert grid["strict_nonoverlap_required"] is True
    assert grid["post_result_case_selection_forbidden"] is True
    assert set(grid["additional_stratified_roles"]) == {
        "WIDE_SEPARATION",
        "SMALL_POSITIVE_GAP",
        "YUKAWA_TRANSITION_RANGE",
    }


def test_production_and_oracle_are_hash_pinned_and_immutable() -> None:
    custody = _report()["comparison_packet_preparation_requirements"][
        "custody_and_immutability"
    ]
    assert all(custody.values())
    assert custody["failed_production_implementation_hash_pin_required"] is True
    assert custody["production_code_changes_during_comparison_forbidden"] is True
    assert custody["oracle_code_changes_during_comparison_forbidden"] is True


def test_component_order_and_convergence_burdens_are_explicit() -> None:
    requirements = _report()["comparison_packet_preparation_requirements"]
    assert requirements["production_order_ladder_to_freeze"] == [8, 16, 24, 32, 40, 48]
    component = requirements["component_comparison"]
    assert component["newtonian_separate"] is True
    assert component["yukawa_separate"] is True
    assert component["analytic_oracle_is_reference"] is True
    assert component["absolute_error_required"] is True
    assert component["relative_error_required"] is True
    assert component["runtime_and_work_required"] is True
    decision = requirements["decision_contract_to_freeze"]
    assert decision["accuracy_plateau_rule_required"] is True
    assert decision["constant_ratio_normalization_probe_required"] is True
    assert decision["geometry_distance_probe_required"] is True
    assert decision["near_threshold_result_is_unresolved"] is True


def test_resource_and_process_bounds_fail_closed() -> None:
    envelope = _report()["comparison_packet_preparation_requirements"][
        "resource_envelope_to_freeze"
    ]
    assert envelope["target_total_wall_clock_seconds_max"] == 1200
    assert envelope["target_memory_mib_max"] == 4096
    assert envelope["per_case_and_per_order_caps_required"] is True
    assert envelope["process_group_termination_required"] is True
    assert envelope["raw_log_and_stage_atomic_records_required"] is True
    assert envelope["budget_exhaustion_fails_closed"] is True


def test_selector_prepares_nothing_and_preserves_all_firewalls() -> None:
    scope = _report()["scope"]
    assert scope["scientific_response_selector_executed"] is True
    assert scope["accepted_oracle_result_frozen"] is True
    assert scope["production_comparison_packet_preparation_authorized"] is True
    assert scope["production_comparison_packet_prepared_now"] is False
    assert scope["production_comparison_executed"] is False
    for key in (
        "oracle_execution_rerun_authorized",
        "production_kernel_repair_authorized",
        "production_kernel_replacement_authorized",
        "torque_or_dft_authorized",
        "final_real_150_vector_authorized",
        "jacobian_or_identifiability_authorized",
        "stage_a_rerun_authorized",
        "stage_b_eligible",
        "stage_b_authorized",
    ):
        assert scope[key] is False, key


def test_selection_gates_next_target_and_human_record_are_exact() -> None:
    report = _report()
    gates = report["selection_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 33
    assert gates["failure_count"] == 0
    assert report["selected_route"] == selection.SELECTED_ROUTE
    assert report["selected_next_target"] == selection.SELECTED_NEXT_TARGET
    human = (ROOT / selection.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        selection.SELECTED_ROUTE,
        selection.SELECTED_NEXT_TARGET,
        "220",
        "160",
        "NO",
        "No label may be selected from visual inspection",
    ):
        assert token in human
