from __future__ import annotations

from formal.python.tools import dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_guardrail_v1_result_review as review


def test_guardrail_v1_review_artifact_is_current() -> None:
    assert review.REVIEW_REPORT_PATH.read_bytes() == review.canonical_json_bytes(review.build_review())


def test_preparation_commit_and_all_six_artifacts_are_immutable() -> None:
    binding = review.bind_preparation()
    assert binding["preparation_commit"] == review.PREPARATION_COMMIT
    assert binding["preparation_parent"] == review.PREPARATION_PARENT
    assert len(binding["bound_preparation_paths"]) == 6
    assert review.PROMPT_DEPENDENCY_ROLE == "DEMOTE_TO_NONBLOCKING_PROVENANCE"


def test_all_rows_and_axes_are_independently_reconstructed() -> None:
    artifact = review.build_review()
    matrix = artifact["independent_matrix_reconstruction"]
    assert matrix["scientific_row_count"] == 14
    assert matrix["unique_row_identity_count"] == 14
    assert matrix["unique_circular_parameter_tuple_count"] == 14
    assert matrix["zero_and_two_pi_duplicate_absent"] is True
    assert matrix["role_counts"] == {"CANONICAL_ANCHOR": 1, "ONE_AT_A_TIME": 10, "INTERACTION_CORNER": 3}
    assert matrix["all_positive_bases_strictly_positive"] is True
    assert matrix["maximum_loading_round_trip_error"] == 1.3877787807814457e-17
    assert matrix["maximum_other_axis_drift"] == 0.0
    assert matrix["all_rows_match_packet"] is True
    assert matrix["multiplicative_loading_symmetry"] is True


def test_all_normalization_regressions_are_reproduced_independently() -> None:
    artifact = review.build_review()
    controls = artifact["independent_normalization_regression_controls"]
    assert [item["control_id"] for item in controls] == review.NORMALIZATION_CONTROL_IDS
    assert len(controls) == 20
    assert all(item["independently_reproduced"] for item in controls)


def test_every_guardrail_mutation_is_isolated() -> None:
    mutation_audit = review.build_review()["independent_mutation_audit"]
    assert mutation_audit["baseline_diagnostics"] == []
    assert len(mutation_audit["mutation_results"]) == 18
    assert mutation_audit["all_eighteen_isolated"] is True
    assert mutation_audit["packet_inventory_matches"] is True
    assert all(item["actual_diagnostics"] == [item["expected_diagnostic"]] for item in mutation_audit["mutation_results"])


def test_materiality_and_numerical_thresholds_remain_separate() -> None:
    protocol = review.build_review()["observable_outcome_and_pilot_audit"]
    assert protocol["scientific_materiality_frozen_before_pilot"] is True
    assert protocol["numerical_thresholds_remain_pending_pilot"] is True
    assert protocol["pilot_scope_is_engineering_only"] is True
    assert protocol["difficult_rows_must_remain"] is True
    assert protocol["classification_order_exact"] is True
    assert protocol["deterministic_precedence_truth_table_cases"] == 32
    assert protocol["every_precedence_case_has_exactly_one_label"] is True


def test_every_review_decision_passes() -> None:
    artifact = review.build_review()
    assert len(artifact["review_decisions"]) == 26
    assert all(artifact["review_decisions"].values())
    assert artifact["accepted"] is True
    assert artifact["verdict"] == review.VERDICT
    assert artifact["preparation_generator_imported"] is False


def test_authority_rotates_only_to_bounded_non_authoritative_pilot() -> None:
    artifact = review.build_review()
    authority = artifact["authority_rotation"]
    assert artifact["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert authority["guardrail_v1_accepted"] is True
    assert authority["bounded_non_authoritative_pilot_authorized"] is True
    assert authority["numerical_threshold_or_parameter_freeze_authorized"] is False
    assert authority["canonical_robustness_execution_authorized"] is False
    assert authority["new_scientific_claim_authorized"] is False
    assert authority["canonical_E_REPRO_result_remains_accepted"] is True
    assert authority["historical_guardrail_v0_rewritten"] is False
    assert authority["historical_signed_axis_rehabilitated"] is False


def test_repository_wide_lean_timeout_is_not_misreported() -> None:
    status = review.build_review()["lean_status_boundary"]
    assert status["direct_affected_preparation_witness"] == "PASSED"
    assert status["repository_wide_aggregate"] == "INCOMPLETE_DUE_TO_600_SECOND_TIMEOUT"
    assert status["jobs_reached_before_timeout"] == 8441
    assert status["jobs_total"] == 8507
    assert status["theorem_error_observed_before_timeout"] is False
    assert status["repository_wide_green_claim_made"] is False
