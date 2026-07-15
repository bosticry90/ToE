from __future__ import annotations

import pytest

from formal.python.tools import dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_non_authoritative_pilot_v1_result_review as review


@pytest.fixture(scope="module")
def artifact() -> dict:
    return review.build_review()


def test_review_artifact_is_current(artifact: dict) -> None:
    assert review.REVIEW_REPORT_PATH.read_bytes() == review.canonical_json_bytes(artifact)


def test_all_nine_pilot_custody_paths_are_bound(artifact: dict) -> None:
    custody = artifact["pilot_custody"]
    assert custody["pilot_commit"] == review.PILOT_COMMIT
    assert custody["pilot_parent"] == review.PILOT_PARENT
    assert len(custody["nine_committed_paths"]) == 9
    assert len(custody["seven_immutable_working_paths"]) == 7
    assert review.sha256_path(review.REPO_ROOT / review.PROMPT_RELATIVE_PATH) == review.PROMPT_SHA256


def test_run_inventory_identities_and_roles_are_independently_reconstructed(
    artifact: dict,
) -> None:
    custody = artifact["independent_run_custody_audit"]
    assert custody["total_record_count"] == custody["unique_run_record_count"] == 50
    assert custody["full_model_record_count"] == 45
    assert custody["forced_comparator_record_count"] == 5
    assert custody["every_row_has_exact_closed_role_set"] is True
    assert custody["all_role_qualified_identities_reconstructed"] is True
    assert custody["no_excluded_or_extra_records"] is True


def test_axes_are_reconstructed_from_the_simulation_payloads(artifact: dict) -> None:
    axes = artifact["independent_axis_audit"]
    assert len(axes["row_audits"]) == 5
    assert axes["maximum_loading_error"] <= review.ROUND_TRIP_TOLERANCE
    assert axes["maximum_other_axis_drift"] <= review.ROUND_TRIP_TOLERANCE
    assert axes["all_positive_bases_strictly_positive"] is True
    assert axes["all_registered_arrays_and_packet_rows_match"] is True


def test_convergence_energy_solver_and_iterations_are_independently_recomputed(
    artifact: dict,
) -> None:
    numerics = artifact["independent_numerical_audit"]
    assert 1.9987 <= numerics["temporal_order_range"][0]
    assert numerics["temporal_order_range"][1] <= 1.9992
    assert 1.9960 <= numerics["energy_error_order_range"][0]
    assert numerics["energy_error_order_range"][1] <= 2.0764
    assert numerics["maximum_solver_to_truncation_ratio"] < 0.01
    assert abs(numerics["maximum_solver_to_truncation_ratio"] - 0.001158328458153041) <= 1e-12
    assert numerics["maximum_solver_iterations_used"] == 9
    assert numerics["maximum_solver_iterations_allowed"] == 80
    assert numerics["all_corrected_bounded_convergent_rules_pass"] is True


def test_classifier_repair_is_traceable_on_the_same_frozen_arrays(artifact: dict) -> None:
    classifier = artifact["classifier_repair_audit"]
    assert classifier["pre_correction_source_blob_bound"] is False
    assert classifier["pre_correction_aggregate_would_block"] is True
    assert classifier["corrected_rule_passes_all_rows"] is True
    assert classifier["same_hash_bound_arrays_used_for_both_predicates"] is True
    assert classifier["correction_is_postprocessing_only_in_final_source"] is True
    assert classifier["accepted_energy_class_unchanged"] is True
    assert classifier["equations_initial_data_rows_and_engineering_sequences_unchanged"] is True
    assert classifier["controls_observables_and_materiality_unchanged"] is True


def test_all_controls_are_independently_reproduced(artifact: dict) -> None:
    controls = artifact["independent_control_audit"]
    assert controls["baseline_diagnostics"] == []
    assert len(controls["positive_controls"]) == 8
    assert len(controls["negative_controls"]) == 13
    assert controls["all_eight_positive_pass"] is True
    assert controls["all_thirteen_negative_fail_for_only_intended_reason"] is True
    assert controls["reported_controls_match"] is True


def test_all_forced_comparators_fail_for_the_expected_source_reason(
    artifact: dict,
) -> None:
    comparators = artifact["independent_comparator_audit"]
    assert len(comparators["comparator_audits"]) == 5
    assert comparators["all_five_exhibit_transverse_failure"] is True
    assert comparators["all_parent_provenance_preserved"] is True
    assert comparators["all_remain_ineligible_for_positive_robustness"] is True
    assert all(item["forced_descendants_remain_zero"] for item in comparators["comparator_audits"])


def test_clean_deterministic_processes_are_reproduced(artifact: dict) -> None:
    determinism = artifact["independent_determinism_audit"]
    assert determinism["execution_count"] == 2
    assert determinism["byte_identical"] is True
    assert determinism["fresh_hashes_match_stored"] is True
    assert determinism["pilot_generator_imported"] is False
    assert determinism["pilot_generator_invoked_only_as_clean_subprocess"] is True


def test_review_accepts_only_freeze_packet_preparation(artifact: dict) -> None:
    assert artifact["accepted"] is True
    assert artifact["verdict"] == review.VERDICT
    assert len(artifact["review_decisions"]) == 18
    assert all(artifact["review_decisions"].values())
    assert artifact["selected_next_target"] == review.SELECTED_NEXT_TARGET
    authority = artifact["authority_rotation"]
    assert authority["pilot_result_accepted_engineering_ready"] is True
    assert authority["calibration_and_full_run_freeze_packet_preparation_authorized"] is True
    assert authority["candidate_parameters_or_thresholds_frozen"] is False
    assert authority["canonical_fourteen_row_robustness_execution_authorized"] is False
    assert authority["robustness_classification_authorized"] is False
    assert authority["descendant_materiality_classification_authorized"] is False
    assert authority["new_E_REPRO_claim_authorized"] is False
