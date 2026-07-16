from __future__ import annotations

import copy

import pytest

from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_design_packet_v1
    as design,
)


@pytest.fixture(scope="module")
def artifacts() -> tuple[dict, dict, dict]:
    return design.build_artifacts()


@pytest.fixture(scope="module")
def packet(artifacts: tuple[dict, dict, dict]) -> dict:
    return artifacts[0]


def test_generated_corrected_design_artifacts_are_current(
    artifacts: tuple[dict, dict, dict],
) -> None:
    packet, manifest, report = artifacts
    assert design.PACKET_PATH.read_bytes() == design.canonical_json_bytes(packet)
    assert design.MANIFEST_PATH.read_bytes() == design.canonical_json_bytes(manifest)
    assert design.REPORT_PATH.read_bytes() == design.canonical_json_bytes(report)


def test_blocked_v0_review_and_canonical_authority_have_exact_custody(
    packet: dict,
) -> None:
    custody = packet["correction_source_custody"]
    assert custody["passed"] is True
    assert custody["correction_source_hashes"] == design.EXPECTED_CORRECTION_SOURCE_HASHES
    assert custody["blocked_v0_review_exact"] is True
    assert custody["blocked_v0_failed_decision_ids"] == design.BLOCKED_V0_DECISION_IDS
    assert custody["blocked_v0_passed_decision_count_preserved"] == 34
    assert custody["canonical_authority_exact"] is True
    assert custody["canonical_run_output_count_checked"] == 203
    assert custody["execution_count_performed"] == 1


def test_corrected_design_preparation_is_read_only_and_does_not_run_simulator(
    packet: dict,
) -> None:
    before = design.canonical_root_digest()
    design.build_artifacts()
    after = design.canonical_root_digest()
    source = (design.REPO_ROOT / design.GENERATOR_RELATIVE_PATH).read_text(
        encoding="utf-8"
    )
    assert before == after == design.EXPECTED_CANONICAL_ROOT_DIGEST
    assert " as simulator" not in source
    assert packet["correction_source_custody"]["new_simulation_run_count"] == 0
    assert packet["correction_source_custody"]["canonical_output_mutation_count"] == 0


def test_all_accepted_v0_scientific_components_are_preserved(packet: dict) -> None:
    preservation = packet["blocked_v0_review_preservation"]
    assert preservation["accepted_decision_count_preserved"] == 34
    assert len(preservation["accepted_decision_ids_preserved"]) == 34
    assert preservation["blocked_decision_ids_corrected"] == design.BLOCKED_V0_DECISION_IDS
    assert preservation["route_selection_reopened"] is False
    assert preservation["scientific_redesign_performed"] is False
    assert packet["inherited_authority"]["selected_route"] == (
        "ROUTE_A_INSTRUMENTED_R13_MECHANISM_EXPERIMENT"
    )
    assert len(packet["scientific_questions"]) == 3
    assert len(packet["required_run_classes"]) == 4
    assert len(packet["mechanism_observable_registry"]) == 14


def test_neighbor_universe_is_all_thirteen_passing_non_R13_rows(packet: dict) -> None:
    neighbor = packet["matched_neighbor_selection_design"]
    expected = {
        "R00_CANONICAL",
        "R01_ETA_WEAK",
        "R02_ETA_STRONG",
        "R03_F_ZERO",
        "R04_F_LOW",
        "R05_F_HIGH",
        "R06_THETA_TRIVIAL",
        "R07_THETA_PARTNER",
        "R08_PHASE_POSITIVE",
        "R09_PHASE_NEGATIVE",
        "R10_MU_HIGH",
        "R11_CORNER_WEAK_HIGH",
        "R12_CORNER_STRONG_ZERO",
    }
    assert set(neighbor["candidate_universe_row_ids"]) == expected
    assert neighbor["all_non_R13_scientific_row_count"] == 13
    assert neighbor["audited_candidate_count"] == 13
    assert neighbor["eligible_candidate_count"] == 13
    assert neighbor["excluded_candidate_ids"] == []
    assert neighbor["axis_sharing_candidate_count"] == 11
    assert neighbor["zero_shared_axis_candidate_count"] == 2
    assert neighbor["zero_shared_axis_candidates_retained"] == [
        "R06_THETA_TRIVIAL",
        "R07_THETA_PARTNER",
    ]
    assert all(
        item["all_applicable_canonical_criteria_pass"]
        and item["all_four_loose_solver_residual_ceilings_pass"]
        for item in neighbor["audited_candidate_universe"]
    )


def test_neighbor_ranking_is_total_deterministic_and_still_unfrozen(packet: dict) -> None:
    neighbor = packet["matched_neighbor_selection_design"]
    assert neighbor["candidate_universe_defined_before_ranking"] is True
    assert neighbor["candidate_universe_matches_ranked_audit"] is True
    assert neighbor["ranking_tuple"] == [
        "negative_shared_axis_count",
        "normalized_distance",
        "scientific_row_id",
    ]
    ranked = neighbor["ranked_candidate_audit"]
    tuples = [tuple(item["rank_tuple"]) for item in ranked]
    assert tuples == sorted(tuples)
    assert ranked[0]["scientific_row_id"] == "R10_MU_HIGH"
    assert neighbor["unique_top_candidate"] is True
    assert neighbor["exact_neighbor_frozen_now"] is False
    assert neighbor["post_result_visual_choice_allowed"] is False


def test_neighbor_universe_mismatch_regression_is_executable(packet: dict) -> None:
    declared = packet["matched_neighbor_selection_design"]["candidate_universe_row_ids"]
    assert design.validate_neighbor_universe_fixture(declared, declared) == []
    audited_axis_sharing_only = [
        row_id
        for row_id in declared
        if row_id not in {"R06_THETA_TRIVIAL", "R07_THETA_PARTNER"}
    ]
    assert design.validate_neighbor_universe_fixture(
        declared, audited_axis_sharing_only
    ) == ["NEIGHBOR_CANDIDATE_UNIVERSE_MISMATCH"]


def test_hypothesis_records_preserve_identity_evidence_criteria_and_reasons(
    packet: dict,
) -> None:
    classifier = packet["hypotheses_and_classifier_design"]
    assert classifier["independently_evaluated_mechanism_ids"] == (
        design.HYPOTHESES_A_TO_D
    )
    schema = classifier["per_hypothesis_decision_schema"]
    assert schema["required_for_hypothesis_ids"] == design.HYPOTHESES_A_TO_D + [
        design.H_E
    ]
    assert schema["required_fields"] == [
        "hypothesis_id",
        "status",
        "evidence_ids",
        "necessary_condition_decisions",
        "supporting_condition_decisions",
        "decision_reasons",
    ]
    assert schema["criterion_decision_fields"] == [
        "criterion_id",
        "status",
        "evidence_ids",
        "reason",
    ]
    h_d = next(
        item
        for item in classifier["hypotheses"]
        if item["hypothesis_id"] == design.HYPOTHESES_A_TO_D[-1]
    )
    assert not any("no H_A" in text for text in h_d["necessary_condition_classes"])


def test_supported_identity_set_is_exact_ordered_and_drives_aggregate(
    packet: dict,
) -> None:
    schema = packet["hypotheses_and_classifier_design"][
        "supported_mechanism_ids_schema"
    ]
    assert schema["required"] is True
    assert schema["allowed_ids"] == design.HYPOTHESES_A_TO_D
    assert schema["duplicates_allowed"] is False
    assert schema["must_equal_exact_supported_status_set"] is True
    assert schema["required_for_single_and_multiple_outcomes"] is True
    statuses = {item: "NOT_SUPPORTED" for item in design.HYPOTHESES_A_TO_D}
    statuses[design.HYPOTHESES_A_TO_D[0]] = "SUPPORTED"
    statuses[design.HYPOTHESES_A_TO_D[2]] = "SUPPORTED"
    statuses[design.HYPOTHESES_A_TO_D[3]] = "SUPPORTED"
    result = design.classify_design_semantics_fixture("EVIDENCE_ADMISSIBLE", statuses)
    assert result["supported_mechanism_ids"] == [
        design.HYPOTHESES_A_TO_D[0],
        design.HYPOTHESES_A_TO_D[2],
        design.HYPOTHESES_A_TO_D[3],
    ]
    assert result["aggregate_mechanism_result"] == "MULTIPLE_SUPPORTED_MECHANISMS"


def test_lost_multiple_mechanism_identities_are_rejected() -> None:
    statuses = {item: "NOT_SUPPORTED" for item in design.HYPOTHESES_A_TO_D}
    statuses[design.HYPOTHESES_A_TO_D[0]] = "SUPPORTED"
    statuses[design.HYPOTHESES_A_TO_D[2]] = "SUPPORTED"
    result = design.classify_design_semantics_fixture("EVIDENCE_ADMISSIBLE", statuses)
    defective = copy.deepcopy(result)
    defective.pop("supported_mechanism_ids")
    assert design.validate_mechanism_result_fixture(
        defective, required_evidence_complete=True
    ) == ["MULTIPLE_MECHANISM_IDENTITY_SET_MISSING"]
    assert design.validate_mechanism_result_fixture(
        result, required_evidence_complete=True
    ) == []


def test_H_E_is_only_complete_admissible_and_nondiscriminating() -> None:
    statuses = {item: "NOT_SUPPORTED" for item in design.HYPOTHESES_A_TO_D}
    unresolved = design.classify_design_semantics_fixture(
        "EVIDENCE_ADMISSIBLE", statuses
    )
    assert unresolved["hypothesis_decisions"][design.H_E]["status"] == "SUPPORTED"
    assert unresolved["supported_mechanism_ids"] == []
    assert unresolved["aggregate_mechanism_result"] == (
        "MECHANISM_UNRESOLVED_COMPLETE_EVIDENCE"
    )
    assert design.validate_mechanism_result_fixture(
        unresolved, required_evidence_complete=True
    ) == []
    assert design.validate_mechanism_result_fixture(
        unresolved, required_evidence_complete=False
    ) == ["INCOMPLETE_EVIDENCE_MISCLASSIFIED_AS_UNRESOLVED"]


def test_missing_required_evidence_blocks_before_hypothesis_evaluation() -> None:
    blocked = design.classify_design_semantics_fixture(
        "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE", {}
    )
    assert blocked["aggregate_mechanism_result"] == "BLOCKED"
    assert blocked["supported_mechanism_ids"] == []
    assert {
        item["status"] for item in blocked["hypothesis_decisions"].values()
    } == {"NOT_EVALUATED"}
    assert blocked["hypothesis_decisions"][design.H_E]["status"] == "NOT_EVALUATED"


def test_fail_closed_precedence_and_two_output_layers_are_exact(packet: dict) -> None:
    classifier = packet["hypotheses_and_classifier_design"]
    assert classifier["evidence_admissibility_outcomes"] == design.EVIDENCE_OUTCOMES
    assert classifier["aggregate_mechanism_outcomes"] == design.AGGREGATE_OUTCOMES
    assert classifier["blocked_outcome_precedence"] == design.EVIDENCE_OUTCOMES[1:]
    assert len(classifier["classifier_precedence"]) == 15
    assert classifier["classifier_precedence"][:6] == [
        "verify design, implementation, and operator custody",
        "verify exact run and payload identities",
        "verify every mandatory output is present",
        "verify instrumentation nonperturbation",
        "verify output units, schemas, norms, and normalization",
        "verify actual discrete-operator bindings",
    ]
    assert classifier["required_evidence_incomplete_routes_to"] == (
        "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE"
    )


def test_permanent_negative_and_positive_controls_cover_all_three_repairs(
    packet: dict,
) -> None:
    controls = packet["permanent_regression_controls"]
    assert [item["expected_diagnostic"] for item in controls["adversarial_controls"]] == [
        "NEIGHBOR_CANDIDATE_UNIVERSE_MISMATCH",
        "MULTIPLE_MECHANISM_IDENTITY_SET_MISSING",
        "INCOMPLETE_EVIDENCE_MISCLASSIFIED_AS_UNRESOLVED",
    ]
    assert len(controls["positive_controls"]) == 5
    assert {item["control_id"] for item in controls["positive_controls"]} == {
        "P_ALL_THIRTEEN_NEIGHBOR_CANDIDATES_AUDITED",
        "P_R10_REMAINS_UNIQUE_TOP_CANDIDATE",
        "P_MULTIPLE_IDENTITIES_RETAINED_EXACTLY",
        "P_COMPLETE_NONDISTINGUISHING_EVIDENCE_SUPPORTS_H_E",
        "P_MISSING_EVIDENCE_BLOCKS_BEFORE_HYPOTHESES",
    }


def test_only_independent_v1_review_is_authorized_next(packet: dict) -> None:
    assert len(packet["freeze_deferred_registry"]) == 16
    assert packet["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
    assert packet["decision_count"] == packet["passed_decision_count"] == 31
    assert packet["failed_decision_ids"] == []
    assert packet["selected_next_target"] == design.SELECTED_NEXT_TARGET
    assert packet["selected_next_target_kind"] == (
        "INDEPENDENT_CORRECTED_DESIGN_REVIEW_ONLY"
    )
    authority = packet["authority_boundary"]
    assert authority["design_packet_prepared"] is True
    assert authority["design_independently_accepted"] is False
    assert authority["numerical_freeze_packet_authorized"] is False
    assert authority["experiment_frozen"] is False
    assert authority["new_simulation_authorized"] is False
    assert authority["rerun_authorized"] is False
    assert authority["robustness_reclassification_authorized"] is False
    assert authority["materiality_classification_authorized"] is False
    assert authority["new_E_REPRO_authorized"] is False
