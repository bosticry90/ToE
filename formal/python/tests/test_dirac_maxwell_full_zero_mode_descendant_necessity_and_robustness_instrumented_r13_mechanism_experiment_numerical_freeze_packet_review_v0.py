from __future__ import annotations

from functools import lru_cache

from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_numerical_freeze_packet_review_v0
    as review,
)


@lru_cache(maxsize=1)
def _report() -> dict:
    return review.build_report()


def test_review_artifact_is_current_and_checkable() -> None:
    assert (review.REPO_ROOT / review.REPORT_RELATIVE_PATH).read_bytes() == review.artifact_bytes()
    assert review.main(["--check"]) == 0


def test_review_blocks_freeze_and_selects_only_versioned_correction() -> None:
    report = _report()
    assert report["verdict"] == review.VERDICT
    assert report["target"] == review.TARGET
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == "VERSIONED_NUMERICAL_FREEZE_CORRECTION_ONLY"
    authority = report["authority_rotation"]
    assert authority["numerical_freeze_v0_accepted"] is False
    assert authority["execution_authorized"] is False
    assert authority["one_time_execution_count_authorized"] == 0
    assert authority["versioned_freeze_correction_authorized"] is True


def test_all_freeze_review_inputs_are_hash_exact() -> None:
    records = _report()["input_custody"]
    assert len(records) == len(review.EXPECTED_INPUT_HASHES)
    assert all(item["passed"] for item in records)


def test_canonical_custody_and_no_execution_state_are_exact() -> None:
    custody = _report()["canonical_custody"]
    assert custody["file_count"] == 205
    assert custody["authority_inventory_digest"] == review.EXPECTED_CANONICAL_ROOT_DIGEST
    assert custody["directory_tree_digest"] == review.EXPECTED_CANONICAL_TREE_DIGEST
    assert custody["canonical_mutation_count"] == 0
    assert custody["mechanism_output_root_absent_before_and_after_review"] is True
    assert not (review.REPO_ROOT / review.EXPERIMENT_OUTPUT_ROOT).exists()


def test_static_six_run_physical_parent_reconstruction_passes() -> None:
    audit = _report()["independent_static_matrix_audit"]
    assert audit["record_count"] == 6
    assert audit["run_ids"] == review.EXPECTED_RUN_IDS
    assert audit["instrumented_count"] == 3
    assert audit["noninstrumented_count"] == 3
    assert audit["all_parent_physical_projections_exact"] is True
    assert audit["all_parent_input_output_identities_exact"] is True
    assert audit["all_three_pairs_exact"] is True


def test_all_six_input_hashes_fail_their_declared_reconstruction_contract() -> None:
    audit = _report()["independent_static_matrix_audit"]
    assert audit["declared_input_hash_contract_pass_count"] == 0
    assert audit["historical_generation_hash_pass_count"] == 6
    for item in audit["declared_input_hash_reconstructions"]:
        assert item["declared_contract_matches"] is False
        assert item["historical_generation_matches"] is True
        assert item["additional_undeclared_exclusion"] == "input_hash_material_excludes"


def test_execution_validator_accepts_all_twenty_identity_mutations() -> None:
    probe = _report()["independent_execution_matrix_validator_probe"]
    assert probe["baseline_diagnostics"] == []
    assert probe["identity_mutation_count"] == 20
    assert probe["incorrectly_accepted_identity_mutation_count"] == 20
    assert all(item["incorrectly_accepted"] for item in probe["identity_mutations"])
    assert probe["dynamics_control_diagnostics"][0].startswith("RUN_MATRIX_N_MISMATCH")
    assert probe["executor_accepts_in_memory_matrix_without_frozen_matrix_sha256"] is True


def test_static_twelve_payload_identity_bijection_itself_passes() -> None:
    audit = _report()["independent_static_matrix_audit"]
    assert audit["role_payload_count"] == 12
    assert audit["all_role_paths_unique"] is True
    assert audit["all_role_paths_NFC"] is True
    assert audit["all_role_paths_casefold_unique"] is True
    assert audit["identity_forward_reverse_maps_exact"] is True
    assert audit["auxiliary_file_count"] == 2
    assert audit["complete_expected_file_count_after_success"] == 14


def test_fourteen_observables_and_eight_blocks_are_statically_registered() -> None:
    audit = _report()["independent_observable_and_operator_audit"]
    assert audit["observable_count"] == 14
    assert audit["observable_ids"] == review.EXPECTED_OBSERVABLE_IDS
    assert audit["all_documentary_semantic_records_complete"] is True
    assert audit["block_count"] == 8
    assert audit["block_ids"] == review.EXPECTED_BLOCK_IDS
    assert audit["packed_span_units_total"] == 22
    assert audit["all_blocks_use_tolerance_scale"] is True
    assert audit["all_block_floors_equal_gamma64"] is True


def test_malformed_raw_observable_payload_is_incorrectly_accepted() -> None:
    probe = _report()["independent_payload_and_classifier_closure_probe"]
    assert probe["malformed_payload_diagnostics"] == []
    assert probe["malformed_payload_with_empty_event_records_is_incorrectly_accepted"] is True


def test_classifier_ignores_wrong_raw_payload_identity_and_content() -> None:
    probe = _report()["independent_payload_and_classifier_closure_probe"]
    assert probe["classifier_ignores_corrupt_raw_payload_fields"] is True
    assert probe["classifier_input_contract_has_no_raw_payload_identity_field"] is True
    assert probe["classifier_baseline_result"] == probe["classifier_corrupted_raw_result"]
    assert probe["classifier_baseline_result"]["evidence_result"] == "EVIDENCE_ADMISSIBLE"


def test_shadow_loaded_modules_are_not_bound_to_hashed_paths() -> None:
    probe = _report()["independent_loaded_module_binding_probe"]
    assert probe["shadow_modules_were_loaded"] is True
    assert probe["workspace_path_hash_report_still_passed"] is True
    assert probe["loaded_module_file_paths_are_not_checked"] is True
    assert probe["evolution_accepted_v0_identity_is_not_checked"] is True


def test_H_C_is_algebraic_and_gamma32_derivation_is_missing() -> None:
    audit = _report()["independent_observable_and_operator_audit"]
    algebra = audit["H_C_algebraic_identity_audit"]
    assert algebra["Q_exact_arithmetic"] == 0
    assert algebra["solver_equation_satisfaction_required_for_identity"] is False
    assert audit["H_C_current_ratio_can_measure_only_floating_evaluation_or_bound_behavior"] is True
    assert audit["gamma32_operation_count_derivation_registered"] is False
    assert audit["exchange_exact_cell_sum_comparison_rule_registered"] is False


def test_hypothesis_threshold_provenance_is_not_complete() -> None:
    audit = _report()["independent_threshold_provenance_audit"]
    assert audit["support_constant_count"] == 23
    assert audit["packet_has_threshold_provenance_registry"] is False
    assert audit["complete_provenance_record_count"] == 0
    assert audit["future_mechanism_outputs_used_as_provenance"] is False


def test_adversarial_contract_and_final_claim_boundary_are_exact() -> None:
    report = _report()
    audit = report["independent_adversarial_coverage_audit"]
    assert audit["required_count"] == 18
    assert audit["registered_count"] == 12
    assert audit["missing_required_count"] == 9
    assert audit["complete"] is False
    assert report["decision_count"] == 48
    assert report["passed_decision_count"] == 41
    assert report["failed_decision_count"] == 7
    assert report["failed_decision_ids"] == review.FAILURE_DECISION_IDS
    assert report["blocking_finding_count"] == 7
    assert report["preserved_scientific_core"]["canonical_robustness"] == "NUMERICALLY_BLOCKED"
    assert report["preserved_scientific_core"]["R13_root_mechanism"] == "UNRESOLVED"
    assert report["preserved_scientific_core"]["new_E_REPRO"] == "NONE"
