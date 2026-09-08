from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v2_result_review as review


ROOT = find_repo_root(Path(__file__))


@pytest.fixture(scope="module")
def report() -> dict:
    return review.build_review()


def test_committed_freeze_v2_custody_is_exact(report: dict) -> None:
    custody = report["freeze_custody"]
    assert custody["committed_path_count"] == 12
    assert custody["immutable_working_path_count"] == 9
    assert custody["freeze_parent"] == review.FREEZE_PARENT


def test_matrix_closes_exactly_at_203_records(report: dict) -> None:
    audit = report["independent_matrix_audit"]
    assert audit["record_count"] == audit["unique_run_id_count"] == 203
    assert audit["role_counts"] == review.EXPECTED_ROLE_COUNTS
    assert audit["all_fourteen_rows_have_exact_thirteen_record_expansion"] is True
    assert audit["all_input_hashes_reconstructed"] is True


def test_all_twenty_two_thresholds_reconstruct_independently(report: dict) -> None:
    audit = report["independent_threshold_audit"]
    assert audit["threshold_count"] == 22
    assert len(audit["reconstructed_threshold_ids"]) == 22
    assert audit["all_values_sources_and_raw_reductions_reconstructed"] is True
    assert audit["all_threshold_schemas_complete"] is True


def test_convergence_classes_are_separate_and_exact(report: dict) -> None:
    audit = report["independent_convergence_audit"]
    assert audit["convergence_class_count"] == 3
    assert audit["Wilson_spatial_class_exact"] is True
    assert audit["temporal_class_exact"] is True
    assert audit["energy_class_exact"] is True
    assert audit["all_fit_members_fixed_for_all_fourteen_rows"] is True


def test_control_applicability_and_feature_representatives_reconstruct(report: dict) -> None:
    audit = report["independent_control_audit"]
    assert audit["control_count"] == 21
    assert audit["positive_count"] == 8
    assert audit["negative_count"] == 13
    assert audit["control_ids_exact"] is True
    assert audit["matrix_contracts_equal_packet_contracts"] is True
    assert audit["feature_dependent_representatives_exact"] is True
    assert audit["all_interaction_corners_receive_row_local_forced_pressure"] is True


def test_identity_closes_across_matrix_manifest_path_and_payload_contract(report: dict) -> None:
    audit = report["independent_identity_audit"]
    assert audit["record_count"] == 203
    assert audit["exact_matrix_manifest_field_reconciliation"] is True
    assert audit["forward_map_exact"] is True
    assert audit["inverse_map_exact"] is True
    assert audit["unique_run_ids_paths_and_casefolded_NFC_filenames"] is True
    assert audit["windows_filenames_legal"] is True
    assert audit["maximum_absolute_path_length"] < 260
    assert audit["payload_echo_contract_exact"] is True


def test_classifier_source_closure_is_hash_bound_and_local_import_free(report: dict) -> None:
    audit = report["independent_classifier_source_audit"]
    assert audit["packet_binding_exact"] is True
    assert audit["manifest_binding_exact"] is True
    assert audit["no_project_local_or_mutable_decision_import"] is True
    assert audit["supplied_decision_fields_explicitly_forbidden"] is True
    assert audit["raw_reconstruction_functions_present"] is True
    assert audit["blocked_materiality_sentinels_present"] is True


def test_classifier_independent_raw_probes_pass(report: dict) -> None:
    audit = report["independent_classifier_probe_audit"]
    assert audit["baseline_deterministic"] is True
    assert audit["baseline_reconstructs_candidate_without_authorizing_claim"] is True
    assert audit["raw_failure_reconstructed_as_numeric_block"] is True
    assert audit["supplied_pass_boolean_rejected_before_use"] is True
    assert audit["missing_output_fails_identity"] is True
    assert audit["wrong_internal_run_id_fails_identity"] is True


def test_mutation_registry_is_not_self_describing(report: dict) -> None:
    audit = report["independent_mutation_atomicity_audit"]
    assert audit["registered_mutation_count"] == audit["unique_mutation_count"] == 23
    assert audit["registry_fields_present"] == ["expected_exact_diagnostic", "mutation_id", "unrelated_prior_failure_forbidden"]
    assert audit["registry_is_independently_self_describing"] is False
    assert audit["all_twenty_three_atomic_and_independently_reconstructible"] is False


@pytest.mark.parametrize(
    "mutation_id",
    [
        "M_V2_COMPARATOR_THRESHOLD_APPLIED_TO_PRIMARY",
        "M_V2_PHASE_CONTROL_MARKED_GLOBAL",
        "M_V2_HOLONOMY_CONTROL_ON_TRIVIAL_ONLY_ROW",
        "M_V2_MATERIALITY_SUPPLIED_AFTER_NUMERICAL_BLOCK",
        "M_V2_SUPPLIED_PASSED_TRUE_WITH_RAW_FAILURE",
    ],
)
def test_each_identified_mutation_has_a_specific_nonatomic_finding(report: dict, mutation_id: str) -> None:
    findings = {item["mutation_id"]: item for item in report["independent_mutation_atomicity_audit"]["non_atomic_or_semantically_mismatched_mutations"]}
    assert findings[mutation_id]["atomic"] is False
    assert findings[mutation_id]["evidence"]


def test_only_mutation_atomicity_decision_blocks(report: dict) -> None:
    failed = [item["decision_id"] for item in report["review_decisions"] if not item["passed"]]
    assert failed == ["all_twenty_three_mutations_atomic_self_describing_and_independently_reconstructible"]
    assert report["all_decisions_passed"] is False


def test_review_verdict_rotates_only_to_freeze_v3(report: dict) -> None:
    assert report["verdict"] == "B-BLOCKED_MUTATION_NONATOMIC"
    assert report["accepted"] is False
    assert report["selected_next_target"] == "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v3"
    authority = report["authority_rotation"]
    assert authority["freeze_v2_accepted"] is False
    assert authority["versioned_freeze_v3_correction_authorized"] is True
    assert authority["additional_pilot_authorized"] is False
    assert authority["canonical_203_record_execution_authorized"] is False


def test_accepted_v2_repairs_remain_preserved(report: dict) -> None:
    assert len(report["preserved_accepted_v2_repairs"]) == 8
    assert "203-record matrix closure" in report["preserved_accepted_v2_repairs"]
    assert "raw-output classifier trust boundary" in report["preserved_accepted_v2_repairs"]


def test_materiality_and_claim_boundary_are_unchanged(report: dict) -> None:
    audit = report["independent_materiality_and_authority_audit"]
    assert all(audit.values())
    assert report["authority_rotation"]["canonical_Maxwell_Dirac_E_REPRO_unchanged"] is True
    assert report["authority_rotation"]["new_E_REPRO_claim_authorized"] is False


def test_review_does_not_import_preparation_or_classifier(report: dict) -> None:
    assert report["freeze_generator_imported"] is False
    assert report["freeze_test_imported"] is False
    assert report["classifier_imported"] is False
    assert report["classifier_invoked_only_in_isolated_subprocess_probes"] is True


def test_validation_status_preserves_environment_sensitive_deselections(report: dict) -> None:
    status = report["validation_status"]
    assert status["current_affected_test_count"] == 119
    assert status["current_affected_tests_passed"] is True
    assert status["historical_environment_sensitive_regeneration_tests_deselected"] == 2
    assert status["freeze_v2_reported_99_test_claim_reproduced_after_commit"] is False
    assert status["artifact_custody_hash_checks_passed"] is True


def test_generated_review_report_is_current(report: dict) -> None:
    path = ROOT / review.REVIEW_REPORT_RELATIVE_PATH
    assert path.read_bytes() == review.canonical_json_bytes(report)


def test_prompt_remains_protected() -> None:
    assert review.PROMPT_DEPENDENCY_ROLE == "DEMOTE_TO_NONBLOCKING_PROVENANCE"
