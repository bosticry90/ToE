from __future__ import annotations

import pytest

from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_canonical_result_review_v2
    as review,
)


@pytest.fixture(scope="module")
def report() -> dict:
    return review.build_review_report()


def test_review_artifact_is_current(report: dict) -> None:
    assert review.REVIEW_REPORT_PATH.read_bytes() == review.canonical_json_bytes(report)


def test_execution_commit_and_all_203_outputs_have_exact_custody(report: dict) -> None:
    custody = report["execution_custody"]
    assert custody["passed"] is True
    assert custody["execution_commit"] == review.EXECUTION_COMMIT
    assert custody["execution_parent"] == review.EXECUTION_PARENT
    assert custody["run_output_count_checked"] == 203
    assert custody["failed_run_ids"] == []
    assert custody["missing_output_root_files"] == []
    assert custody["orphan_output_root_files"] == []


def test_exact_record_identity_and_registered_payload_hashes_reproduce(report: dict) -> None:
    identity = report["identity_and_completeness_reconstruction"]
    assert identity["passed"] is True
    assert identity["record_count"] == identity["identity_count"] == identity["payload_count"] == 203
    assert identity["scientific_record_count"] == 182
    assert identity["positive_control_count"] == 8
    assert identity["negative_control_count"] == 13
    assert identity["identity_failures"] == []
    assert identity["input_hash_failures"] == []
    assert identity["registered_numerical_payload_hash_failures"] == []


def test_all_controls_reconstruct_from_raw_observations(report: dict) -> None:
    controls = report["control_reconstruction"]
    assert controls["passed"] is True
    assert controls["positive_control_count"] == 8
    assert controls["negative_control_count"] == 13
    assert len(controls["control_ids_reconstructed"]) == 21
    assert controls["failed_control_ids"] == []
    assert all(item["passed"] for item in controls["control_results"])


def test_exact_four_threshold_failures_are_only_R13_loose_solver(report: dict) -> None:
    thresholds = report["threshold_reconstruction"]
    assert thresholds["frozen_threshold_count"] == 22
    assert thresholds["numerical_floor_count"] == 2
    assert thresholds["threshold_decision_count"] == 3416
    assert thresholds["passing_threshold_decision_count"] == 3412
    assert thresholds["failing_threshold_decision_count"] == 4
    assert {item["run_id"] for item in thresholds["failures"]} == {review.R13_LOOSE_RUN}
    assert {item["threshold_id"] for item in thresholds["failures"]} == set(
        review.R13_FAILED_KEYS.values()
    )
    assert all(item["initial_magnitude"] <= item["frozen_limit"] for item in thresholds["failures"])
    assert all(item["maximum_time"] == pytest.approx(0.05) for item in thresholds["failures"])


def test_convergence_determinism_solver_and_model_domain_gates_pass(report: dict) -> None:
    convergence = report["convergence_reconstruction"]
    assert convergence["passed"] is True
    assert convergence["evaluation_count"] == 42
    assert convergence["failures"] == []
    assert convergence["orders_by_row"][review.R13]["minimum_spatial_descendant_order"] >= 0.8
    assert convergence["orders_by_row"][review.R13]["minimum_temporal_descendant_order"] >= 1.5
    assert convergence["orders_by_row"][review.R13]["minimum_energy_error_order"] >= 1.5
    assert report["determinism_reconstruction"]["passed"] is True
    assert report["solver_reconstruction"]["passed"] is True
    assert report["model_domain_reconstruction"]["passed"] is True
    assert report["model_domain_reconstruction"]["R13_model_domain_margin"] > 0.0


def test_R13_is_tolerance_dependent_not_a_model_domain_result(report: dict) -> None:
    diagnosis = report["R13_independent_diagnosis"]
    assert diagnosis["failed_run_id"] == review.R13_LOOSE_RUN
    assert diagnosis["all_four_initial_values_pass"] is True
    assert diagnosis["all_four_failures_are_monotone_secular_in_absolute_magnitude"] is True
    assert diagnosis["primary_passes_same_four_residual_ceilings"] is True
    tolerance_rows = {item["solver_tolerance"]: item for item in diagnosis["solver_tolerance_scan"]}
    assert tolerance_rows[1e-8]["all_four_residual_ceilings_pass"] is False
    assert tolerance_rows[1e-10]["all_four_residual_ceilings_pass"] is True
    assert tolerance_rows[1e-12]["all_four_residual_ceilings_pass"] is True
    assert diagnosis["solver_hierarchy"]["solver_to_truncation_ratio"] <= 0.01
    assert diagnosis["model_domain_limit_observed"] is False
    assert diagnosis["independent_explanation_class"] == "TOLERANCE_DEPENDENT_NUMERICAL_ADMISSIBILITY_BLOCK"


def test_neighbor_comparison_is_descriptive_and_all_axis_sharing_rows_pass(report: dict) -> None:
    diagnosis = report["R13_independent_diagnosis"]
    neighbors = diagnosis["neighbor_rows_sharing_at_least_one_axis_value"]
    assert len(neighbors) == 11
    assert diagnosis["all_axis_sharing_neighbors_pass_same_loose_solver_residual_ceilings"] is True
    assert all(item["all_four_residual_ceilings_pass"] for item in neighbors)


def test_candidate_reproduces_but_materiality_remains_suppressed(report: dict) -> None:
    result = report["independent_classifier_reconstruction"]
    assert report["candidate_artifact_matches_independent_reconstruction"] is True
    assert result["robustness_status"] == "NUMERICALLY_BLOCKED"
    assert result["numerically_blocked_rows"] == [review.R13]
    assert result["descendant_significance_status"] == "NOT_EVALUATED_NUMERICAL_BLOCK"
    assert report["materiality_evaluation"]["materiality_function_called"] is False


def test_review_accepts_only_the_numerically_blocked_result(report: dict) -> None:
    assert report["review_completed"] is True
    assert report["accepted"] is True
    assert report["verdict"] == "ACCEPT_NUMERICALLY_BLOCKED_CANONICAL_RESULT"
    assert report["accepted_claim_label"] == "B-BLOCKED"
    assert report["scientific_robustness_status"] == "NUMERICALLY_BLOCKED"
    assert report["descendant_materiality_status"] == "NOT_EVALUATED_NUMERICAL_BLOCK"
    assert report["passed_decision_count"] == report["decision_count"] == 20
    assert report["failed_decision_ids"] == []
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert report["authority_rotation"]["new_E_REPRO_claim_authorized"] is False
    assert report["authority_rotation"]["interpretation_driven_rerun_authorized"] is False
    assert report["authority_rotation"]["model_domain_limit_claim_authorized"] is False


def test_stale_execution_nonclaim_is_disclosed_without_rewriting_execution(report: dict) -> None:
    note = report["documentary_note"]
    assert note["stale_pre_execution_nonclaim_detected"] is True
    assert note["raw_execution_effect"] == "NONE"
    assert review.sha256_path(review.REPO_ROOT / review.EXECUTION_REPORT) == review.EXPECTED_CORE_HASHES[
        review.EXECUTION_REPORT
    ]
