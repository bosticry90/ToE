from __future__ import annotations

import pytest

from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_r13_numerical_block_diagnostic_packet_review_v0
    as review,
)


@pytest.fixture(scope="module")
def report() -> dict:
    return review.build_review_report()


def test_review_artifact_is_current(report: dict) -> None:
    assert review.REPORT_PATH.read_bytes() == review.canonical_json_bytes(report)


def test_review_is_independent_read_only_and_does_not_import_the_packet_generator(
    report: dict,
) -> None:
    before = review.canonical_root_digest()
    review.build_review_report()
    after = review.canonical_root_digest()
    source = (review.REPO_ROOT / review.REVIEWER_RELATIVE_PATH).read_text(encoding="utf-8")
    assert before == after == review.EXPECTED_CANONICAL_ROOT_DIGEST
    assert " as diagnostic" not in source
    assert " as simulator" not in source
    assert report["source_custody"]["simulation_invocation_count_during_review"] == 0
    assert report["source_custody"]["canonical_output_mutation_authorized"] is False


def test_diagnostic_artifacts_and_all_canonical_outputs_have_exact_custody(
    report: dict,
) -> None:
    custody = report["source_custody"]
    assert custody["passed"] is True
    assert custody["source_artifact_hashes"] == review.EXPECTED_SOURCE_HASHES
    assert custody["diagnostic_packet_hash_bound_by_manifest"] is True
    assert custody["diagnostic_generator_hash_bound_by_manifest"] is True
    assert custody["diagnostic_report_hashes_match_packet_manifest_and_generator"] is True
    assert custody["canonical_run_output_count_checked"] == 203
    assert custody["canonical_run_output_hash_failures"] == []
    assert custody["canonical_root_file_count"] == 205
    assert custody["canonical_root_digest"] == review.EXPECTED_CANONICAL_ROOT_DIGEST
    assert custody["execution_count_performed"] == 1


def test_four_timelines_reproduce_exact_crossing_order_monotonicity_and_final_maxima(
    report: dict,
) -> None:
    timelines = report["independent_failure_timeline_reconstruction"]
    assert timelines["sample_count"] == 17
    assert len(timelines["timelines"]) == 4
    assert timelines["all_initial_values_pass"] is True
    assert timelines["all_absolute_magnitudes_monotone_nondecreasing"] is True
    assert timelines["all_maxima_at_final_time"] is True
    assert [item["time"] for item in timelines["threshold_crossing_order"]] == pytest.approx(
        [0.0125, 0.03125, 0.04375]
    )
    assert timelines["threshold_crossing_order"][0]["threshold_ids"] == [
        "maximum_continuity_residual",
        "maximum_longitudinal_Maxwell_residual",
    ]
    assert report["packet_parity_and_claim_audit"]["timeline_reconstruction_exact"]


def test_time_growth_audit_finds_three_linear_and_one_time_squared_without_extrapolation(
    report: dict,
) -> None:
    audit = report["independent_timing_and_time_law_audit"]
    assert audit["linear_in_time_preferred_count"] == 3
    assert audit["linear_in_time_squared_preferred_count"] == 1
    by_id = {
        item["threshold_id"]: item["better_of_these_two_descriptive_coordinates"]
        for item in audit["ordinary_scale_linear_vs_time_squared"]
    }
    assert by_id["maximum_exchange_longitudinal_residual"] == "LINEAR_IN_TIME_SQUARED"
    assert by_id["maximum_Gauss_residual"] == "LINEAR_IN_TIME"
    assert by_id["maximum_continuity_residual"] == "LINEAR_IN_TIME"
    assert by_id["maximum_longitudinal_Maxwell_residual"] == "LINEAR_IN_TIME"
    assert audit["common_time_law_certified"] is False
    assert audit["longer_duration_prediction_executed"] is False
    assert audit["causal_hierarchy_certified"] is False


def test_all_and_only_preregistered_comparable_tolerance_roles_enter_fit(report: dict) -> None:
    response = report["independent_tolerance_response_reconstruction"]
    assert response["registered_tolerance_run_ids"] == review.TOLERANCE_RUN_IDS
    assert response["registered_tolerances_used"] == [1e-8, 1e-10, 1e-12]
    assert response["post_hoc_tolerance_point_selection_performed"] is False
    assert response["configurations_identical_except_tolerance_and_identity_fields"] is True
    assert len(set(response["normalized_configuration_hashes"].values())) == 1


def test_exact_tolerance_maxima_and_exponent_range_reproduce(report: dict) -> None:
    response = report["independent_tolerance_response_reconstruction"]
    assert response["all_four_residual_maxima_strictly_decrease_with_tighter_tolerance"]
    assert response["overall_exponent_minimum"] == pytest.approx(0.7448900948221593)
    assert response["overall_exponent_maximum"] == pytest.approx(0.7559176564888908)
    assert response["overall_exponent_median"] == pytest.approx(0.7486818198236936)
    assert response["physical_or_asymptotic_exponent_claim_authorized"] is False
    assert report["packet_parity_and_claim_audit"][
        "tolerance_numeric_reconstruction_exact"
    ]


def test_solver_histories_reproduce_constant_iterations_and_no_late_growth(
    report: dict,
) -> None:
    response = report["independent_tolerance_response_reconstruction"]
    rows = {item["solver_tolerance"]: item for item in response["solver_runs"]}
    assert rows[1e-8]["maximum_iterations"] == 3
    assert rows[1e-10]["maximum_iterations"] == 4
    assert rows[1e-12]["maximum_iterations"] == 5
    assert all(item["late_iteration_increase"] == 0 for item in rows.values())
    assert response["all_solver_iteration_histories_constant_after_initial_state"]
    assert response["all_solver_residual_histories_nonincreasing_after_first_step"]
    assert response["all_steps_converged"]


def test_eleven_neighbors_and_each_individual_axis_match_reproduce(report: dict) -> None:
    neighbors = report["independent_neighbor_reconstruction"]
    assert neighbors["axis_sharing_neighbor_count"] == 11
    assert neighbors["all_axis_sharing_neighbors_pass"] is True
    assert all(item["all_four_pass"] for item in neighbors["axis_sharing_neighbors"])
    assert neighbors[
        "all_five_individual_axis_values_have_at_least_one_passing_non_R13_match"
    ]
    assert neighbors["individual_axis_value_sufficient_cause_supported"] is False
    assert neighbors["unique_interaction_order_identified"] is False
    assert report["packet_parity_and_claim_audit"]["neighbor_reconstruction_exact"]


def test_three_root_mechanism_questions_are_absent_across_all_203_outputs(
    report: dict,
) -> None:
    availability = report["independent_mechanism_data_availability_audit"]
    for key in (
        "exact_field_matter_cancellation_kappa",
        "equation_block_solver_dominance",
        "discrete_Maxwell_to_continuity_closure",
    ):
        item = availability[key]
        assert item["status"] == "NOT_DERIVABLE_FROM_PRESERVED_OUTPUTS"
        assert item["present_fields"] == []
        assert item["missing_fields"] == item["required_fields"]
        assert item["checked_across_canonical_record_count"] == 203
    precision = availability["higher_precision_arithmetic_contribution"]
    assert precision["status"] == "NOT_TESTABLE_WITH_EXISTING_DOUBLE_PRECISION_OUTPUTS_ONLY"
    assert availability["root_numerical_mechanism_identified"] is False


def test_packet_claim_ceiling_contains_no_physical_causal_or_robustness_promotion(
    report: dict,
) -> None:
    audit = report["packet_parity_and_claim_audit"]
    assert audit["claim_ceiling_preserved"] is True
    assert audit["causal_hierarchy_overclaim_detected"] is False
    assert audit["physical_instability_overclaim_detected"] is False
    assert audit["model_boundary_overclaim_detected"] is False
    assert audit["conditional_robustness_overclaim_detected"] is False
    assert audit["new_E_REPRO_overclaim_detected"] is False


def test_review_accepts_pattern_but_preserves_block_and_unresolved_mechanism(
    report: dict,
) -> None:
    assert report["accepted"] is True
    assert report["verdict"] == (
        "ACCEPT_R13_NUMERICAL_BLOCK_DIAGNOSTIC_PATTERN_ROOT_MECHANISM_UNRESOLVED"
    )
    assert report["canonical_robustness_status"] == "NUMERICALLY_BLOCKED"
    assert report["diagnostic_pattern_status"] == (
        "ACCEPTED_TOLERANCE_DEPENDENT_LONGITUDINAL_PATTERN"
    )
    assert report["root_numerical_mechanism_status"] == "UNRESOLVED"
    assert report["descendant_materiality_status"] == "NOT_EVALUATED_NUMERICAL_BLOCK"
    assert report["passed_decision_count"] == report["decision_count"] == 25
    assert report["failed_decision_ids"] == []


def test_authority_rotates_only_to_bounded_route_selection(report: dict) -> None:
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    authority = report["authority_rotation"]
    assert authority["diagnostic_pattern_accepted"] is True
    assert authority["route_selection_packet_authorized"] is True
    assert authority["exact_root_mechanism_identified"] is False
    assert authority["new_simulation_authorized"] is False
    assert authority["rerun_authorized"] is False
    assert authority["threshold_or_fit_change_authorized"] is False
    assert authority["robustness_reclassification_authorized"] is False
    assert authority["materiality_classification_authorized"] is False
    assert authority["new_E_REPRO_authorized"] is False
