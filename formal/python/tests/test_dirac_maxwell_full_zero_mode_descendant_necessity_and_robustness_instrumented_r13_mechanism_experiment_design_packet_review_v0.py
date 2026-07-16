from __future__ import annotations

import pytest

from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_design_packet_review_v0
    as review,
)


@pytest.fixture(scope="module")
def report() -> dict:
    return review.build_review_report()


def test_review_artifact_is_current(report: dict) -> None:
    assert review.REPORT_PATH.read_bytes() == review.canonical_json_bytes(report)


def test_review_is_independent_read_only_and_invokes_no_simulator(report: dict) -> None:
    before = review.canonical_root_digest()
    review.build_review_report()
    after = review.canonical_root_digest()
    source = (review.REPO_ROOT / review.REVIEWER_RELATIVE_PATH).read_text(encoding="utf-8")
    assert before == after == review.EXPECTED_CANONICAL_ROOT_DIGEST
    assert "import dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_design_packet_v0" not in source
    assert "import simulator" not in source
    assert report["source_custody"]["simulation_invocation_count_during_review"] == 0


def test_design_artifacts_and_all_canonical_outputs_have_exact_custody(report: dict) -> None:
    custody = report["source_custody"]
    assert custody["passed"] is True
    assert custody["source_artifact_hashes"] == review.EXPECTED_SOURCE_HASHES
    assert custody["design_artifact_cross_bindings_exact"] is True
    assert custody["live_target_and_accepted_route_authority_exact"] is True
    assert custody["prepared_design_has_27_of_27_decisions"] is True
    assert custody["canonical_run_output_count_checked"] == 203
    assert custody["canonical_run_output_hash_failures"] == []
    assert custody["canonical_root_file_count"] == 205
    assert custody["canonical_root_digest"] == review.EXPECTED_CANONICAL_ROOT_DIGEST
    assert custody["execution_count_performed"] == 1


def test_four_roles_and_three_comparisons_are_scientifically_sufficient(report: dict) -> None:
    sufficiency = report["independent_scientific_sufficiency_review"]
    assert sufficiency["scientific_question_count"] == 3
    assert sufficiency["mechanism_ids_exact"] is True
    assert sufficiency["required_role_class_count"] == 4
    assert sufficiency["all_three_comparisons_directly_answerable"] is True
    assert sufficiency["all_three_mechanism_questions_have_observable_coverage"] is True
    assert sufficiency["scientifically_sufficient"] is True


def test_fourteen_observables_are_unique_traced_and_preserve_mechanism_structure(
    report: dict,
) -> None:
    minimality = report["independent_minimality_and_semantics_review"]
    assert minimality["observable_count"] == 14
    assert minimality["observable_ids_exact_and_unique"] is True
    assert minimality["untraced_observable_ids"] == []
    assert minimality["invalid_mechanism_ids"] == []
    assert minimality["all_observables_have_semantics_units_and_question_trace"] is True
    assert minimality["time_space_and_iteration_structure_preserved"] is True
    assert minimality["per_step_raw_series_required"] is True
    assert minimality["per_block_freeze_semantics_complete"] is True
    assert minimality["required_missing_data_is_blocking"] is True


def test_each_root_mechanism_question_has_direct_observable_coverage(report: dict) -> None:
    mechanism = report["independent_mechanism_specific_sufficiency"]
    assert mechanism["exchange_question_directly_answerable"] is True
    assert mechanism["equation_block_question_directly_answerable"] is True
    assert mechanism["discrete_closure_question_directly_answerable"] is True


def test_hypothesis_structure_has_two_blocking_discrimination_defects(report: dict) -> None:
    hypotheses = report["independent_hypothesis_discrimination_review"]
    assert hypotheses["hypothesis_ids_exact"] is True
    assert hypotheses["outcome_classes_exact"] is True
    assert hypotheses["multiple_mechanisms_allowed"] is True
    assert hypotheses["forced_single_winner_forbidden"] is True
    assert hypotheses["unresolved_outcome_mandatory"] is True
    assert hypotheses["custody_completeness_and_numerical_gates_precede_hypotheses"]
    assert hypotheses["A_to_C_require_predeclared_contrast_not_self_definition_alone"]
    assert hypotheses["per_hypothesis_support_vector_and_criterion_records_required"] is False
    assert hypotheses["H_E_is_disjoint_from_required_evidence_incompleteness"] is False


def test_nonperturbation_contract_is_strong_and_failure_is_blocking(report: dict) -> None:
    nonperturbation = report["independent_nonperturbation_review"]
    assert nonperturbation["read_only_separate_channel"] is True
    assert nonperturbation[
        "all_solver_state_order_stopping_timestep_equation_and_parameter_mutations_forbidden"
    ] is True
    assert nonperturbation["capture_occurs_after_evolution_on_a_copy"] is True
    assert nonperturbation["every_core_configuration_has_paired_reference"] is True
    assert nonperturbation["primary_rule_is_trajectory_level_byte_identity"] is True
    assert nonperturbation["fallback_is_not_defined_or_authorized"] is True
    assert nonperturbation["fallback_floor_and_ceiling_must_be_independently_frozen"]
    assert nonperturbation["failure_blocks_mechanism_classification"] is True


def test_discrete_closure_requires_actual_implemented_operators(report: dict) -> None:
    operators = report["independent_discrete_operator_authenticity_review"]
    assert operators["continuum_formula_rejected_as_audit_definition"] is True
    assert operators["posthoc_continuum_substitution_forbidden"] is True
    assert operators["actual_operator_outputs_and_scheme_closure_observables_required"]
    assert operators["implemented_scheme_features_are_all_named"] is True
    assert operators[
        "implementation_mapping_operator_hashes_units_remainder_and_controls_required"
    ] is True
    assert operators["formula_and_threshold_deferred"] is True
    assert operators["failure_to_close_definition_before_freeze_is_blocking"] is True


def test_neighbor_ranking_reproduces_but_eligibility_prose_is_ambiguous(report: dict) -> None:
    neighbor = report["independent_neighbor_selection_reconstruction"]
    assert neighbor["candidate_count"] == 11
    assert neighbor["packet_ranking_exact"] is True
    assert neighbor["unique_top_candidate"] is True
    assert neighbor["provisional_top_candidate"] == "R10_MU_HIGH"
    assert neighbor["provisional_top_matches_packet"] is True
    assert neighbor["future_result_data_used"] is False
    assert neighbor["exact_neighbor_frozen_by_design"] is False
    assert neighbor["top_shared_axis_count"] == 2
    assert neighbor["declared_eligibility_explicitly_requires_axis_sharing"] is False
    assert "not a one-axis-isolated control" in neighbor["scientific_limitation"]


def test_sixteen_values_remain_deferred_and_support_modules_are_secondary(
    report: dict,
) -> None:
    separation = report["independent_design_freeze_separation_review"]
    assert separation["freeze_deferred_item_count"] == 16
    assert separation["all_sixteen_freeze_items_present"] is True
    assert separation["no_forbidden_authority_true"] is True
    assert separation["exact_run_count_or_values_selected"] is False
    assert separation["exact_neighbor_frozen"] is False
    assert separation["closure_formula_or_threshold_frozen"] is False
    assert separation["supporting_B_and_C_are_secondary_options"] is True


def test_output_custody_is_separate_and_no_execution_occurred(report: dict) -> None:
    output = report["independent_output_and_nonexecution_review"]
    assert output["new_output_family_required"] is True
    assert output["canonical_output_root_write_allowed"] is False
    assert output["new_output_root_created"] is False
    assert output["new_mechanism_output_created"] is False
    assert output["payload_identity_field_count"] == 13
    assert output["fixed_logging_and_blocking_output_failure_contract"] is True
    assert output["design_generator_imports_no_simulator"] is True
    assert output["design_generator_invokes_no_subprocess"] is True
    assert output["new_simulation_count"] == 0
    assert output["canonical_output_mutation_count"] == 0
    assert output["canonical_root_digest_unchanged"] is True


def test_review_blocks_on_exactly_three_bounded_specification_defects(report: dict) -> None:
    assert report["review_completed"] is True
    assert report["accepted"] is False
    assert report["verdict"] == "BLOCK_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_DESIGN"
    assert report["accepted_claim_label"] == "B-BLOCKED"
    assert report["decision_count"] == 37
    assert report["passed_decision_count"] == 34
    assert report["failed_decision_ids"] == [
        "classifier_preserves_per_hypothesis_support_vector_and_criterion_records",
        "H_E_is_disjoint_from_required_evidence_completeness_block",
        "neighbor_eligibility_prose_matches_axis_sharing_candidate_universe",
    ]
    assert [item["finding_id"] for item in report["blocking_findings"]] == [
        "B_NEIGHBOR_ELIGIBILITY_SCOPE_AMBIGUOUS",
        "B_PER_HYPOTHESIS_DECISION_VECTOR_MISSING",
        "B_H_E_OVERLAPS_COMPLETENESS_GATE",
    ]


def test_blocked_review_preserves_current_target_and_withholds_all_authority(
    report: dict,
) -> None:
    assert report["selected_next_target"] == review.TARGET
    authority = report["authority_rotation"]
    assert authority["instrumented_R13_experiment_design_accepted"] is False
    assert authority["numerical_freeze_packet_preparation_authorized"] is False
    assert authority["numerical_freeze_packet_prepared"] is False
    assert authority["numerical_freeze_accepted"] is False
    assert authority["experiment_frozen"] is False
    assert authority["exact_run_count_or_values_selected"] is False
    assert authority["new_simulation_authorized"] is False
    assert authority["rerun_authorized"] is False
    assert authority["robustness_reclassification_authorized"] is False
    assert authority["materiality_classification_authorized"] is False
    assert authority["new_E_REPRO_authorized"] is False


def test_report_preserves_freeze_requirements_without_preparing_a_freeze(report: dict) -> None:
    obligations = report["freeze_packet_preparation_obligations"]
    assert len(obligations["observable_semantic_record_fields"]) == 15
    assert len(obligations["must_close_before_freeze_review"]) == 8
    assert "blocks freeze acceptance" in obligations["freeze_failure_disposition"]
    assert report["canonical_robustness_status"] == "NUMERICALLY_BLOCKED"
    assert report["root_numerical_mechanism_status"] == "UNRESOLVED"
    assert report["descendant_materiality_status"] == "NOT_EVALUATED_NUMERICAL_BLOCK"
