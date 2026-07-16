from __future__ import annotations

import pytest

from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_r13_numerical_block_route_selection_packet_review_v0
    as review,
)


@pytest.fixture(scope="module")
def report() -> dict:
    return review.build_review_report()


def test_review_artifact_is_current(report: dict) -> None:
    assert review.REPORT_PATH.read_bytes() == review.canonical_json_bytes(report)


def test_review_is_independent_read_only_and_does_not_import_route_generator(
    report: dict,
) -> None:
    before = review.canonical_root_digest()
    review.build_review_report()
    after = review.canonical_root_digest()
    source = (review.REPO_ROOT / review.REVIEWER_RELATIVE_PATH).read_text(encoding="utf-8")
    assert before == after == review.EXPECTED_CANONICAL_ROOT_DIGEST
    assert " as selection" not in source
    assert " as simulator" not in source
    assert report["source_custody"]["simulation_invocation_count_during_review"] == 0


def test_route_artifacts_and_all_203_canonical_outputs_have_exact_custody(
    report: dict,
) -> None:
    custody = report["source_custody"]
    assert custody["passed"] is True
    assert custody["source_artifact_hashes"] == review.EXPECTED_SOURCE_HASHES
    assert custody["route_artifact_cross_bindings_exact"] is True
    assert custody["live_target_and_downstream_target_exact"] is True
    assert custody["accepted_diagnostic_authority_exact"] is True
    assert custody["canonical_run_output_count_checked"] == 203
    assert custody["canonical_run_output_hash_failures"] == []
    assert custody["canonical_root_file_count"] == 205
    assert custody["canonical_root_digest"] == review.EXPECTED_CANONICAL_ROOT_DIGEST
    assert custody["execution_count_performed"] == 1


def test_independent_capability_matrix_reconstructs_route_A_as_direct_3_of_3(
    report: dict,
) -> None:
    coverage = report["independent_coverage_review"]
    rows = {item["route_id"]: item for item in coverage["capability_matrix"]}
    route_a = rows[review.ROUTE_IDS[0]]
    assert route_a["cancellation_conditioning"] == "DIRECT"
    assert route_a["equation_block_dominance"] == "DIRECT"
    assert route_a["discrete_Maxwell_continuity_closure"] == "DIRECT"
    assert route_a["direct_coverage_count"] == 3
    assert coverage["only_route_A_has_complete_direct_coverage"] is True
    assert coverage["direct_coverage_counts_match_packet"] is True
    assert all(rows[route_id]["direct_coverage_count"] == 0 for route_id in review.ROUTE_IDS[1:])


def test_supporting_indirect_partial_and_fallback_routes_are_distinguished(
    report: dict,
) -> None:
    coverage = report["independent_coverage_review"]
    rows = {item["route_id"]: item for item in coverage["capability_matrix"]}
    assert coverage["route_B_and_C_supporting_not_primary"] is True
    assert rows[review.ROUTE_IDS[1]]["cancellation_conditioning"] == "NONE"
    assert rows[review.ROUTE_IDS[2]]["equation_block_dominance"] == "NONE"
    assert rows[review.ROUTE_IDS[3]]["cancellation_conditioning"] == "INDIRECT"
    assert rows[review.ROUTE_IDS[3]]["discrete_Maxwell_continuity_closure"] == (
        "POSSIBLY_INDIRECT"
    )
    assert rows[review.ROUTE_IDS[4]]["cancellation_conditioning"] == "PARTIAL"
    assert coverage["route_F_no_new_data_fallback_recognized"] is True


def test_route_A_scope_changes_instrumentation_not_model_method_or_parameters(
    report: dict,
) -> None:
    scope = report["independent_scope_review"]
    assert scope["scope_passed"] is True
    assert scope["physical_equations_unchanged"] is True
    assert scope["numerical_method_unchanged"] is True
    assert scope["diagnostic_instrumentation_expanded"] is True
    assert scope["initial_condition_change_authorized"] is False
    assert scope["R13_parameter_change_authorized"] is False
    assert scope["different_solver_authorized"] is False
    assert scope["threshold_or_fit_change_authorized"] is False
    assert scope["robustness_reclassification_authorized"] is False
    assert scope["materiality_evaluation_authorized"] is False


def test_every_mandatory_observable_is_necessary_and_all_mechanisms_are_covered(
    report: dict,
) -> None:
    trace = report["independent_observable_traceability_review"]
    assert trace["mandatory_observable_count"] == 9
    assert trace["all_mandatory_observables_trace_to_unresolved_questions"] is True
    assert trace["all_three_mechanism_questions_covered"] is True
    assert trace["untraced_mandatory_observables"] == []
    assert all(item["traces_to_mechanism_ids"] for item in trace["traceability_rows"])


def test_future_controls_retain_loose_tight_neighbor_and_canonical_separation(
    report: dict,
) -> None:
    trace = report["independent_observable_traceability_review"]
    assert trace["historically_failing_loose_role_retained_as_future_design_obligation"]
    assert trace["tight_reference_retained_as_future_design_obligation"]
    assert trace["matched_passing_neighbor_required"]
    assert trace["new_outputs_must_remain_outside_canonical_root"]


def test_downstream_design_requires_five_competing_hypotheses_including_unresolved(
    report: dict,
) -> None:
    downstream = report["downstream_design_packet_requirements"]
    assert [item["hypothesis_id"] for item in downstream["competing_hypotheses_required"]] == [
        "H_A_CANCELLATION_CONDITIONING",
        "H_B_LONGITUDINAL_EQUATION_BLOCK_DOMINANCE",
        "H_C_DISCRETE_CLOSURE_MISMATCH",
        "H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR",
        "H_E_UNRESOLVED_MECHANISM",
    ]
    assert downstream["status"] == (
        "REQUIREMENTS_FOR_DESIGN_PACKET_PREPARATION_NOT_A_FROZEN_DESIGN"
    )


def test_downstream_design_requires_nonperturbation_self_control_and_real_operators(
    report: dict,
) -> None:
    downstream = report["downstream_design_packet_requirements"]
    assert downstream["instrumentation_self_control_required"] is True
    assert "may not alter solver variables" in downstream[
        "instrumentation_nonperturbation_requirement"
    ]
    assert downstream[
        "actual_discrete_operators_required_not_posthoc_continuum_surrogates"
    ] is True
    assert downstream["exchange_conditioning_floor_and_units_must_be_frozen"] is True
    assert downstream["per_block_definition_requirements"] == [
        "mathematical definition",
        "units",
        "norm",
        "normalization",
        "spatial aggregation",
        "time aggregation",
    ]


def test_packet_contains_no_execution_result_or_new_classification(report: dict) -> None:
    audit = report["independent_nonexecution_review"]
    assert audit["all_forbidden_authority_values_false"] is True
    assert audit["execution_count_preserved"] is True
    assert audit["canonical_output_root_unchanged"] is True
    assert audit["new_simulation_output_count"] == 0
    assert audit["new_tolerance_result_count"] == 0
    assert audit["new_duration_result_count"] == 0
    assert audit["new_solver_comparison_result_count"] == 0
    assert audit["new_classification_count"] == 0


def test_review_accepts_route_A_but_preserves_block_materiality_and_unknown_mechanism(
    report: dict,
) -> None:
    assert report["accepted"] is True
    assert report["verdict"] == (
        "ACCEPT_R13_NUMERICAL_BLOCK_ROUTE_SELECTION_ROUTE_A_DESIGN_PREPARATION_ONLY"
    )
    assert report["accepted_claim_label"] == "POLICY_ROUTE_SELECTION_ONLY"
    assert report["selected_route"] == review.ROUTE_IDS[0]
    assert report["canonical_robustness_status"] == "NUMERICALLY_BLOCKED"
    assert report["root_numerical_mechanism_status"] == "UNRESOLVED"
    assert report["descendant_materiality_status"] == "NOT_EVALUATED_NUMERICAL_BLOCK"
    assert report["passed_decision_count"] == report["decision_count"] == 26
    assert report["failed_decision_ids"] == []


def test_authority_rotates_only_to_design_packet_preparation(report: dict) -> None:
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    authority = report["authority_rotation"]
    assert authority["route_selection_accepted"] is True
    assert authority["instrumented_R13_design_packet_preparation_authorized"] is True
    assert authority["experiment_design_accepted"] is False
    assert authority["experiment_freeze_authorized"] is False
    assert authority["experiment_frozen"] is False
    assert authority["new_simulation_authorized"] is False
    assert authority["rerun_authorized"] is False
    assert authority["different_numerical_method_authorized"] is False
    assert authority["R13_parameter_or_initial_condition_change_authorized"] is False
    assert authority["robustness_reclassification_authorized"] is False
    assert authority["materiality_classification_authorized"] is False
    assert authority["new_E_REPRO_authorized"] is False
