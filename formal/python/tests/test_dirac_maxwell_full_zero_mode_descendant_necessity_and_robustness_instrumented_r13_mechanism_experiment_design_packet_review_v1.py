from __future__ import annotations

import copy

import pytest

from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_design_packet_review_v1
    as review,
)


@pytest.fixture(scope="module")
def report() -> dict:
    return review.build_review_report()


def test_generated_independent_review_artifact_is_current(report: dict) -> None:
    assert review.REPORT_PATH.read_bytes() == review.canonical_json_bytes(report)


def test_all_bound_sources_and_cross_bindings_have_exact_custody(report: dict) -> None:
    custody = report["source_custody"]
    assert custody["passed"] is True
    assert custody["source_artifact_hashes"] == review.EXPECTED_SOURCE_HASHES
    assert custody["all_source_artifact_hashes_exact"] is True
    assert custody["design_artifact_cross_bindings_exact"] is True
    assert custody["live_corrected_design_review_authority_exact"] is True
    assert custody["prepared_design_has_31_of_31_decisions"] is True
    assert custody["canonical_result_authority_exact"] is True


def test_independent_review_is_read_only_and_preserves_canonical_execution(report: dict) -> None:
    before = review.canonical_root_digest()
    review.build_review_report()
    after = review.canonical_root_digest()
    assert before == after == review.EXPECTED_CANONICAL_ROOT_DIGEST
    custody = report["source_custody"]
    assert custody["canonical_run_output_count_checked"] == 203
    assert custody["canonical_run_output_hash_failures"] == []
    assert custody["canonical_root_file_count"] == 205
    assert custody["execution_count_performed"] == 1
    assert custody["simulation_invocation_count_during_review"] == 0
    assert custody["canonical_output_mutation_count"] == 0


def test_review_accepts_design_only_and_authorizes_freeze_preparation_only(
    report: dict,
) -> None:
    assert report["review_completed"] is True
    assert report["accepted"] is True
    assert report["verdict"] == "ACCEPT_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_DESIGN"
    assert report["accepted_claim_label"] == "POLICY_EXPERIMENT_DESIGN_ONLY"
    assert report["blocking_findings"] == []
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    authority = report["authority_rotation"]
    assert authority["instrumented_R13_experiment_design_accepted"] is True
    assert authority["numerical_freeze_packet_preparation_authorized"] is True
    assert authority["numerical_freeze_packet_prepared"] is False
    assert authority["numerical_freeze_accepted"] is False
    assert authority["experiment_frozen"] is False
    assert authority["new_simulation_authorized"] is False


def test_v0_pass_ledger_and_legacy_classifier_supersession_are_explicit(
    report: dict,
) -> None:
    boundary = report["independent_preservation_and_freeze_boundary_review"]
    assert boundary["accepted_v0_pass_ledger_ids_exact"] is True
    assert boundary["only_three_blocked_decision_ids_named_as_corrected"] is True
    assert boundary["legacy_classifier_subconditions_are_explicitly_bounded"] is True
    legacy = boundary["legacy_classifier_supersession"]
    assert all(legacy.values())
    assert boundary[
        "preservation_term_is_reviewed_as_pass_ledger_and_experiment_core_not_verbatim_classifier_predicates"
    ] is True


def test_route_roles_observables_and_accepted_scientific_sections_are_preserved(
    report: dict,
) -> None:
    boundary = report["independent_preservation_and_freeze_boundary_review"]
    assert boundary[
        "all_nine_accepted_scientific_sections_byte_semantically_unchanged"
    ] is True
    assert set(boundary["preserved_section_results"]) == set(
        review.PRESERVED_SECTION_IDS
    )
    assert all(boundary["preserved_section_results"].values())
    decisions = {item["decision_id"]: item["passed"] for item in report["decisions"]}
    assert decisions[
        "Route_A_three_questions_four_roles_and_fourteen_observables_are_preserved"
    ] is True
    assert decisions["instrumentation_nonperturbation_contract_is_preserved"] is True
    assert decisions["actual_discrete_operator_closure_contract_is_preserved"] is True


def test_all_thirteen_candidates_are_reconstructed_from_immutable_evidence(
    report: dict,
) -> None:
    neighbor = report["independent_neighbor_selection_reconstruction"]
    assert neighbor["candidate_count"] == 13
    assert neighbor["audited_candidate_count"] == 13
    assert neighbor["all_candidates_pass_canonical_criteria"] is True
    assert neighbor["all_candidates_pass_four_linked_ceilings"] is True
    assert neighbor["packet_candidate_universe_exact"] is True
    assert neighbor["packet_candidate_audit_exact"] is True
    assert len(neighbor["frozen_linked_ceiling_values"]) == 4
    assert all(
        item["historical_loose_output_sha256"]
        and item["historical_loose_run_id"].endswith("SOLVER_TOL1eM08")
        for item in neighbor["independent_candidate_audit"]
    )


def test_independent_ranking_matches_packet_and_R10_is_unique(report: dict) -> None:
    neighbor = report["independent_neighbor_selection_reconstruction"]
    ranked = neighbor["independent_ranked_candidates"]
    assert neighbor["ranking_tuple_exact"] is True
    assert neighbor["packet_ranking_exact"] is True
    assert neighbor["unique_top_candidate"] is True
    assert neighbor["provisional_top_candidate"] == "R10_MU_HIGH"
    assert neighbor["provisional_top_matches_packet"] is True
    assert ranked[0]["rank_tuple"] == [
        -2,
        0.8816610347670144,
        "R10_MU_HIGH",
    ]
    assert ranked[1]["scientific_row_id"] == "R12_CORNER_STRONG_ZERO"


def test_zero_shared_rows_are_retained_and_neighbor_remains_unfrozen(report: dict) -> None:
    neighbor = report["independent_neighbor_selection_reconstruction"]
    assert neighbor["axis_sharing_candidate_count"] == 11
    assert neighbor["zero_shared_axis_candidate_ids"] == [
        "R06_THETA_TRIVIAL",
        "R07_THETA_PARTNER",
    ]
    assert neighbor["exact_neighbor_frozen"] is False
    assert neighbor["future_mechanism_result_data_used"] is False


def test_H_D_is_a_positive_independent_hypothesis_not_a_fallback(report: dict) -> None:
    classifier = report["independent_classifier_contract_review"]
    assert classifier["H_A_through_H_D_independently_evaluated"] is True
    assert classifier["H_D_has_positive_distributed_evidence_criteria"] is True
    assert classifier["H_D_is_not_a_fallback_for_A_through_C_failure"] is True
    fixture = report["independent_adversarial_regression_reconstruction"][
        "positive_H_D_only_result"
    ]
    assert fixture["supported_mechanism_ids"] == [review.HYPOTHESES_A_TO_D[-1]]
    assert fixture["aggregate_mechanism_result"] == "SINGLE_SUPPORTED_MECHANISM"


def test_individual_decision_and_support_set_schemas_preserve_mechanism_identity(
    report: dict,
) -> None:
    classifier = report["independent_classifier_contract_review"]
    assert classifier["hypothesis_ids_exact"] is True
    assert classifier["per_hypothesis_required_ids_exact"] is True
    assert classifier["per_hypothesis_required_fields_exact"] is True
    assert classifier["criterion_record_fields_exact"] is True
    assert classifier["aggregate_cannot_replace_individual_records"] is True
    assert classifier["support_set_allowed_ids_and_order_exact"] is True
    assert classifier["support_set_required_unique_and_exact"] is True
    assert classifier["multiple_support_allowed_without_forced_winner"] is True


def test_fail_closed_precedence_and_H_E_completeness_gate_are_exact(report: dict) -> None:
    classifier = report["independent_classifier_contract_review"]
    assert classifier["evidence_outcomes_exact"] is True
    assert classifier["aggregate_outcomes_exact"] is True
    assert classifier["blocked_semantics_exact"] is True
    assert classifier["precedence_exact"] is True
    assert classifier["H_E_requires_complete_admissible_empty_support_set"] is True
    assert classifier["missing_required_evidence_blocks_first"] is True


def test_neighbor_universe_mismatch_mutation_is_reconstructed_independently(
    report: dict,
) -> None:
    regressions = report["independent_adversarial_regression_reconstruction"]
    assert regressions["candidate_universe_mutation_diagnostic"] == [
        "NEIGHBOR_CANDIDATE_UNIVERSE_MISMATCH"
    ]
    declared = report["independent_neighbor_selection_reconstruction"][
        "independently_reconstructed_candidate_ids"
    ]
    assert review.validate_neighbor_universe_fixture(declared, declared) == []
    assert review.validate_neighbor_universe_fixture(declared, declared[:-2]) == [
        "NEIGHBOR_CANDIDATE_UNIVERSE_MISMATCH"
    ]


def test_lost_multiple_mechanism_identity_mutation_is_reconstructed_independently(
    report: dict,
) -> None:
    regressions = report["independent_adversarial_regression_reconstruction"]
    assert regressions["lost_identity_mutation_diagnostic"] == [
        "MULTIPLE_MECHANISM_IDENTITY_SET_MISSING"
    ]
    statuses = {item: "NOT_SUPPORTED" for item in review.HYPOTHESES_A_TO_D}
    statuses[review.HYPOTHESES_A_TO_D[0]] = "SUPPORTED"
    statuses[review.HYPOTHESES_A_TO_D[2]] = "SUPPORTED"
    valid = review.construct_mechanism_fixture("EVIDENCE_ADMISSIBLE", statuses)
    defective = copy.deepcopy(valid)
    defective.pop("supported_mechanism_ids")
    assert review.validate_mechanism_fixture(
        defective, required_evidence_complete=True
    ) == ["MULTIPLE_MECHANISM_IDENTITY_SET_MISSING"]


def test_incomplete_evidence_as_H_E_mutation_is_reconstructed_independently(
    report: dict,
) -> None:
    regressions = report["independent_adversarial_regression_reconstruction"]
    assert regressions["incomplete_as_unresolved_mutation_diagnostic"] == [
        "INCOMPLETE_EVIDENCE_MISCLASSIFIED_AS_UNRESOLVED"
    ]
    unresolved = regressions["positive_complete_unresolved_result"]
    assert review.validate_mechanism_fixture(
        unresolved, required_evidence_complete=False
    ) == ["INCOMPLETE_EVIDENCE_MISCLASSIFIED_AS_UNRESOLVED"]


def test_positive_multiple_unresolved_H_D_and_blocked_fixtures_are_exact(
    report: dict,
) -> None:
    regressions = report["independent_adversarial_regression_reconstruction"]
    assert regressions["all_three_adversarial_diagnostics_exact"] is True
    assert regressions["positive_multiple_preserves_exact_ids"] is True
    assert regressions["positive_H_D_is_single_positive_hypothesis"] is True
    assert regressions[
        "positive_complete_nondiscriminating_supports_H_E"
    ] is True
    assert regressions["positive_missing_evidence_suppresses_all_hypotheses"] is True
    assert regressions["registered_adversarial_control_count"] == 3
    assert regressions["registered_positive_control_count"] == 5


def test_design_freeze_boundary_contains_no_hidden_future_execution_defaults(
    report: dict,
) -> None:
    boundary = report["independent_preservation_and_freeze_boundary_review"]
    assert boundary["all_sixteen_items_deferred"] is True
    assert boundary["no_forbidden_authority_true"] is True
    assert boundary["forbidden_authority_values_true"] == {}
    assert boundary["exact_neighbor_unfrozen"] is True
    assert boundary["closure_formula_and_threshold_unfrozen"] is True
    assert boundary["future_classifier_constants_remain_deferred"] is True
    assert boundary["exact_future_run_matrix_or_tolerances_selected"] is False
    assert boundary["design_generator_imports_no_simulator"] is True
    assert boundary["design_generator_invokes_no_subprocess"] is True
    assert boundary["design_generator_creates_no_mechanism_output_root"] is True


def test_historical_tolerances_are_provenance_not_new_freeze_values(report: dict) -> None:
    boundary = report["independent_preservation_and_freeze_boundary_review"]
    rules = boundary["historical_tolerances_are_provenance_not_future_selection"]
    assert len(rules) == 3
    assert "historically failing" in rules[0]
    assert "historically passing" in rules[1]
    assert "historical loose-solver role" in rules[2]
    interpretation = report["review_interpretation"]["historical_anchor_interpretation"]
    assert "read-only eligibility evidence" in interpretation
    assert "do not select the future run matrix" in interpretation


def test_decisions_claim_ceiling_and_current_scientific_authority_are_exact(
    report: dict,
) -> None:
    assert report["decision_count"] == report["passed_decision_count"] == 43
    assert report["failed_decision_ids"] == []
    assert all(item["passed"] for item in report["decisions"])
    assert report["canonical_robustness_status"] == "NUMERICALLY_BLOCKED"
    assert report["root_numerical_mechanism_status"] == "UNRESOLVED"
    assert report["descendant_materiality_status"] == (
        "NOT_EVALUATED_NUMERICAL_BLOCK"
    )
    authority = report["authority_rotation"]
    for key in [
        "numerical_freeze_packet_prepared",
        "numerical_freeze_accepted",
        "experiment_frozen",
        "exact_run_count_or_values_selected",
        "new_simulation_authorized",
        "rerun_authorized",
        "robustness_reclassification_authorized",
        "materiality_classification_authorized",
        "new_E_REPRO_authorized",
        "pillar_or_seam_promotion_authorized",
        "C_k_dynamics_authorized",
        "CCFT_promotion_authorized",
        "master_action_promotion_authorized",
    ]:
        assert authority[key] is False
