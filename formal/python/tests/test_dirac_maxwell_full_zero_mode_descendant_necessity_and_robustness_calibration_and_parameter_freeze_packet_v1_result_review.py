from __future__ import annotations

import pytest

from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v1_result_review
    as review,
)


@pytest.fixture(scope="module")
def report() -> dict:
    return review.build_review()


def test_review_report_is_current(report: dict) -> None:
    assert review.REVIEW_REPORT_PATH.read_bytes() == review.canonical_json_bytes(report)


def test_committed_freeze_custody_is_exact(report: dict) -> None:
    custody = report["freeze_custody"]
    assert custody["freeze_commit"] == review.FREEZE_COMMIT
    assert custody["freeze_parent"] == review.FREEZE_PARENT
    assert custody["ten_committed_paths"] == review.EXPECTED_FREEZE_HASHES
    assert len(custody["immutable_working_paths_verified"]) == 8
    assert review.sha256_path(review.REPO_ROOT / review.PROMPT_RELATIVE_PATH) == review.PROMPT_SHA256
    assert report["freeze_generator_imported"] is False
    assert report["classifier_imported"] is False


def test_all_203_matrix_records_reconstruct(report: dict) -> None:
    audit = report["independent_matrix_audit"]
    assert audit["record_count"] == audit["unique_run_id_count"] == audit["unique_output_path_count"] == 203
    assert audit["role_counts_exact"] is True
    assert audit["all_required_record_fields_present"] is True
    assert audit["scientific_row_ids_exact"] is True
    assert audit["scientific_axis_tuples_exact"] is True
    assert audit["all_fourteen_rows_have_exact_uniform_expansion"] is True
    assert audit["packet_matrix_hash_exact"] is True
    assert audit["manifest_matrix_hash_exact"] is True


def test_all_twenty_two_threshold_values_reconstruct_but_scope_is_incomplete(report: dict) -> None:
    audit = report["independent_threshold_audit"]
    assert audit["threshold_count"] == 22
    assert audit["all_twenty_two_values_and_source_sets_reconstructed"] is True
    assert audit["every_threshold_has_explicit_eligible_run_roles"] is False
    assert audit["every_threshold_declares_units_or_normalization"] is False
    assert audit["global_raw_threshold_scope_is_justified_across_all_fourteen_rows"] is False


def test_spatial_gate_conflicts_with_accepted_Wilson_order_class(report: dict) -> None:
    audit = report["independent_convergence_audit"]
    assert audit["proposed_measured_minima_match"] is True
    assert audit["accepted_canonical_freeze_review_verdict"] == "ACCEPT_FREEZE"
    assert audit["accepted_spatial_metric"] == "final_phi2_l2"
    assert audit["accepted_spatial_minimum_order"] == 0.8
    assert audit["accepted_spatial_reason"] == "Wilson artifact is leading O(a)"
    assert audit["proposed_spatial_minimum_order"] == 1.5
    assert audit["spatial_gate_matches_accepted_analytic_order_class"] is False
    assert audit["temporal_gate_matches_accepted_second_order_class"] is True
    assert audit["energy_gate_matches_accepted_second_order_class"] is True


def test_classifier_hash_is_bound_but_scientific_data_closure_is_not(report: dict) -> None:
    audit = report["independent_classifier_audit"]
    assert audit["packet_hash_binding_exact"] is True
    assert audit["manifest_hash_binding_exact"] is True
    assert audit["no_mutable_scientific_decision_import"] is True
    assert audit["deterministic_probe_byte_equivalent"] is True
    assert audit["arbitrary_fourteen_unique_row_ids_are_incorrectly_accepted"] is True
    assert audit["classifier_checks_exact_frozen_row_identity_set"] is False
    assert audit["classifier_derives_custody_controls_convergence_and_threshold_passes_from_203_outputs"] is False
    assert audit["unkeyed_empty_materiality_vectors_are_incorrectly_accepted"] is True
    assert audit["classifier_data_closure_complete"] is False


def test_blocked_classifier_outcome_cannot_carry_materiality(report: dict) -> None:
    audit = report["independent_classifier_audit"]
    probe = audit["no_passing_subdomain_probe"]
    assert probe["robustness_status"] == "NUMERICALLY_BLOCKED"
    assert probe["descendant_significance_status"] == "INTERMEDIATE_DESCENDANT_CONTRIBUTION"
    assert audit["blocked_outcome_incorrectly_receives_significance"] is True


def test_control_ids_and_forced_comparators_are_complete_but_scope_is_not(report: dict) -> None:
    audit = report["independent_control_audit"]
    assert audit["positive_control_count"] == 8
    assert audit["negative_control_count"] == 13
    assert audit["row_local_forced_comparator_count"] == 14
    assert audit["positive_control_ids_exact"] is True
    assert audit["negative_control_ids_exact"] is True
    assert audit["forced_comparator_present_for_every_scientific_row"] is True
    assert audit["every_control_declares_global_anchor_row_or_conditional_scope"] is False
    assert audit["all_thirteen_negative_controls_are_attached_only_to_anchor"] is True
    assert audit["control_coverage_complete"] is False


def test_current_filename_set_is_safe_but_identity_contract_is_incomplete(report: dict) -> None:
    audit = report["independent_filename_audit"]
    assert audit["matrix_is_bijective_for_current_203_records"] is True
    assert audit["unique_filename_count"] == audit["casefolded_NFC_unique_filename_count"] == 203
    assert audit["all_current_filenames_legal_on_windows"] is True
    assert audit["current_paths_below_260_characters"] is True
    assert audit["maximum_absolute_path_length"] == 190
    assert audit["manifest_points_to_hash_bound_matrix"] is True
    assert audit["manifest_contains_explicit_run_id_to_output_path_map"] is False
    assert audit["output_payload_must_echo_exact_run_id"] is False


def test_materiality_values_and_claim_ceiling_remain_correct(report: dict) -> None:
    audit = report["independent_materiality_and_claim_audit"]
    assert audit["material_gate_exact"] is True
    assert audit["dominated_gate_exact"] is True
    assert audit["sensitivity_values_exact"] is True
    assert audit["robustness_and_significance_fields_separate_in_packet"] is True
    assert audit["canonical_execution_unauthorized"] is True
    assert audit["new_claim_unauthorized"] is True
    assert audit["canonical_E_REPRO_unchanged"] is True
    assert audit["nonpromotion_ceiling_preserved"] is True


def test_review_preserves_all_blockers_and_selects_only_v2_correction(report: dict) -> None:
    assert report["verdict"] == "B-BLOCKED_CONVERGENCE_CLASS_MISMATCH"
    assert report["accepted"] is False
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == "VERSIONED_FREEZE_CORRECTION_ONLY"
    assert [item["diagnostic"] for item in report["blocking_diagnostics"]] == [
        "B-BLOCKED_CONVERGENCE_CLASS_MISMATCH",
        "B-BLOCKED_THRESHOLD_SCOPE",
        "B-BLOCKED_CLASSIFIER_CUSTODY",
        "B-BLOCKED_CONTROL_COVERAGE",
        "B-BLOCKED_FILENAME_IDENTITY_MAPPING",
    ]
    assert all(item["pilot_rerun_required"] is False for item in report["blocking_diagnostics"])
    authority = report["authority_rotation"]
    assert authority["freeze_v1_accepted"] is False
    assert authority["versioned_freeze_v2_correction_authorized"] is True
    assert authority["additional_pilot_authorized"] is False
    assert authority["canonical_203_record_execution_authorized"] is False
    assert authority["robustness_classification_authorized"] is False
    assert authority["descendant_materiality_classification_authorized"] is False
    assert authority["new_E_REPRO_claim_authorized"] is False


def test_historical_repository_build_remains_incomplete(report: dict) -> None:
    lean = report["lean_status_boundary"]
    assert lean["affected_freeze_preparation_build"] == {"status": "PASSED", "job_count": 142}
    assert lean["affected_review_authority_build"] == {"status": "PASSED", "job_count": 143}
    historical = lean["historical_repository_wide_aggregate"]
    assert historical["completed_jobs"] == 8441
    assert historical["total_jobs"] == 8507
    assert historical["status"] == "INCOMPLETE"
    assert historical["theorem_error_observed_before_timeout"] is False
    assert lean["repository_wide_green_claim"] is False
    validation = report["validation_status"]
    assert validation == {
        "affected_test_count": 53,
        "affected_tests_passed": True,
        "artifact_checks_passed": True,
        "authority_surface_parity_passed": True,
        "tooling_validation_passed": True,
    }
