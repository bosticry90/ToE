from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.tests.strict_physics_state_helpers import (
    README_PATH,
    REPO_ROOT,
    STATE_PATH,
    STRICT_MAP_PATH,
    active_workstream,
    assert_current_target_consistent,
    assert_focused_gate_not_manifest_enrolled,
    assert_forbidden_promotions_closed,
    assert_frontier_matches_registry,
    assert_historical_target_recorded,
    assert_public_surfaces_match_registry,
    loop_registry,
    read_text,
    workstream,
)


CANDIDATE_SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMStatEntropyAssumptionReductionCandidateSelection.lean"
)
POST_SELECTOR_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostQMStatEntropyAssumptionMapBoundedAttackSelection.lean"
)
MAP_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMStatEntropySemanticsSupportingAssumptionMap.lean"
)
AGGREGATE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_CANDIDATE_SELECTION_20260510_v0.json"
)
POST_SELECTOR_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "POST_QM_STAT_ENTROPY_ASSUMPTION_MAP_BOUNDED_ATTACK_SELECTION_20260510_v0.json"
)
MAP_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP_20260510_v0.json"
)
CURRENT_AUTHORITATIVE_SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)

REPORT_ID = "QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_CANDIDATE_SELECTION_20260510_v0"
SURFACE_ID = "qm_stat_entropy_assumption_reduction_candidate_selection_v0"
ACTIVE_LANE = "qm_stat_entropy_assumption_reduction_candidate_selection"
PREVIOUS_LANE = "post_qm_stat_entropy_assumption_map_bounded_attack_selection"
CONSUMED_TARGET = "prepare_qm_stat_entropy_assumption_reduction_candidate_selection"
CONSUMED_SELECTOR_TOKEN = "POST_QM_STAT_ENTROPY_ASSUMPTION_MAP_NEXT_ATTACK_SELECTED"
RESULT_TOKEN = "QM_STAT_ENTROPY_ASSUMPTION_REDUCTION_CANDIDATE_SELECTED"
SELECTED_TARGET = "prepare_selected_qm_stat_entropy_assumption_reduction_bounded_attack"
SELECTED_CANDIDATE = "log_domain_zero_handling_convention_required"
SECOND_CANDIDATE = "normalization_or_probability_mass_condition_required"
SELECTED_GAP = "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_THEOREM_GAP_v0"
SELECTED_OBLIGATION = "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_OBLIGATION_v0"
SELECTION_EVIDENCE = str(CANDIDATE_SELECTION_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
POST_SELECTOR_EVIDENCE = str(POST_SELECTOR_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
MAP_EVIDENCE = str(MAP_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
POST_SELECTOR_REPORT_EVIDENCE = str(
    POST_SELECTOR_REPORT_PATH.relative_to(REPO_ROOT)
).replace("\\", "/")
MAP_REPORT_EVIDENCE = str(MAP_REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
EXPECTED_CRITERIA = {
    "local_formalizability",
    "risk_of_overclaim",
    "dependency_count",
    "representable_as_lean_definition_or_structure",
    "materially_clarifies_supplied_only_entropy_gap",
}
EXPECTED_ASSUMPTIONS = {
    "target_entropy_functional_definition_required",
    "statistical_state_domain_semantics_required",
    "normalization_or_probability_mass_condition_required",
    "finite_support_or_summability_condition_required",
    "log_domain_zero_handling_convention_required",
    "transport_alignment_relation_required",
    "residual_zero_bridge_condition_required",
    "comparison_target_semantics_required",
}


def _read(path: Path) -> str:
    return read_text(path)


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def test_qm_stat_entropy_assumption_reduction_candidate_selection_surface_records_choice() -> None:
    text = _read(CANDIDATE_SELECTION_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        CONSUMED_SELECTOR_TOKEN,
        RESULT_TOKEN,
        SELECTED_TARGET,
        SELECTED_CANDIDATE,
        SECOND_CANDIDATE,
        "QMStatEntropyAssumptionReductionCandidateSelectionStatus",
        "QMStatEntropyAssumptionReductionCandidateRow",
        "QMStatEntropyAssumptionReductionSelectionCriterion",
        "qm_stat_entropy_assumption_reduction_candidate_selection_consumes_live_target_v0",
        "qm_stat_entropy_assumption_reduction_candidate_selection_consumes_selector_token_v0",
        "qm_stat_entropy_assumption_reduction_candidate_selection_result_token_v0",
        "qm_stat_entropy_assumption_reduction_candidate_selection_next_target_v0",
        "qm_stat_entropy_assumption_reduction_candidate_selection_all_8_evaluated_v0",
        "qm_stat_entropy_assumption_reduction_candidate_selection_exactly_one_v0",
        "qm_stat_entropy_assumption_reduction_candidate_selection_selected_candidate_v0",
        "qm_stat_entropy_assumption_reduction_candidate_selection_frontier_target_v0",
    } | EXPECTED_CRITERIA | EXPECTED_ASSUMPTIONS:
        assert token in text

    assert (
        "import ToeFormal.Derivation.QMStatEntropyAssumptionReductionCandidateSelection"
        in aggregate_text
    )


def test_qm_stat_entropy_assumption_reduction_candidate_selection_surface_preserves_nonclaims() -> None:
    text = _read(CANDIDATE_SELECTION_PATH)

    for theorem in {
        "qm_stat_entropy_assumption_reduction_candidate_selection_does_not_execute_reduction_v0",
        "qm_stat_entropy_assumption_reduction_candidate_selection_no_assumption_discharge_v0",
        "qm_stat_entropy_assumption_reduction_candidate_selection_no_lean_backed_discharge_v0",
        "qm_stat_entropy_assumption_reduction_candidate_selection_supplied_only_preserved_v0",
        "qm_stat_entropy_assumption_reduction_candidate_selection_no_gap_closure_v0",
        "qm_stat_entropy_assumption_reduction_candidate_selection_no_qm_stat_completion_v0",
        "qm_stat_entropy_assumption_reduction_candidate_selection_no_seam_closure_v0",
        "qm_stat_entropy_assumption_reduction_candidate_selection_no_phase2_readiness_v0",
        "qm_stat_entropy_assumption_reduction_candidate_selection_no_empirical_adequacy_v0",
        "qm_stat_entropy_assumption_reduction_candidate_selection_no_canonical_toe_claim_v0",
        "qm_stat_entropy_assumption_reduction_candidate_selection_master_action_not_promoted_v0",
        "qm_stat_entropy_assumption_reduction_candidate_selection_qft_gr_not_authorized_v0",
        "qm_stat_entropy_assumption_reduction_candidate_selection_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_qm_stat_entropy_assumption_reduction_candidate_selection_report_records_ranking() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["selection_status"] == "completed_candidate_selection_only"
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_selector_token"] == CONSUMED_SELECTOR_TOKEN
    assert report["result_token"] == RESULT_TOKEN
    assert report["selected_next_target"] == SELECTED_TARGET
    assert report["source_selector_surface"] == POST_SELECTOR_EVIDENCE
    assert report["source_selector_report"] == POST_SELECTOR_REPORT_EVIDENCE
    assert report["source_map_surface"] == MAP_EVIDENCE
    assert report["source_map_report"] == MAP_REPORT_EVIDENCE
    assert report["selection_surface"] == SELECTION_EVIDENCE
    assert report["focused_gate"] == (
        "formal/python/tests/test_qm_stat_entropy_assumption_reduction_candidate_selection_gate.py"
    )
    assert report["authorized_effect"] == (
        "SELECT_EXACTLY_ONE_ASSUMPTION_REDUCTION_CANDIDATE"
    )
    assert report["reduction_executed"] is False
    assert report["selection_count"] == 1
    assert report["assumption_class_count"] == 8
    assert set(report["selection_criteria"]) == EXPECTED_CRITERIA

    rankings = report["candidate_rankings"]
    assert len(rankings) == 8
    assert {row["assumption_class_id"] for row in rankings} == EXPECTED_ASSUMPTIONS
    assert [row["rank"] for row in rankings] == list(range(1, 9))
    selected = [row for row in rankings if row["selection"] == "selected"]
    assert len(selected) == 1
    assert selected[0]["assumption_class_id"] == SELECTED_CANDIDATE
    assert selected[0]["rank"] == 1
    assert selected[0]["authority_before_selection"] == "not yet represented"
    assert selected[0]["dependency_count"] == 1
    assert selected[0]["lean_definition_or_structure_fit"] is True

    assert report["selected_candidate"] == {
        "assumption_class_id": SELECTED_CANDIDATE,
        "assumption_class_label": "log-domain / zero-handling convention required",
        "authority_before_selection": "not yet represented",
        "rank": 1,
        "reason": (
            "The log-domain and zero-probability convention is absent, locally "
            "representable as a small Lean definition or structure, low dependency, "
            "and directly clarifies the entropy functional semantics without "
            "asserting theorem discharge."
        ),
    }


def test_qm_stat_entropy_assumption_reduction_candidate_selection_report_preserves_boundary() -> None:
    report = _json(REPORT_PATH)

    assert report["nonclaim_boundaries"] == {
        "all_8_assumption_classes_evaluated": True,
        "exactly_one_candidate_selected": True,
        "reduction_executed": False,
        "assumption_discharge_claim": False,
        "target_stat_entropy_semantics_lean_backed": False,
        "target_stat_entropy_semantics_supplied_only": True,
        "entropy_semantics_theorem_discharged": False,
        "qm_stat_pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "phase2_readiness_claim": False,
        "empirical_adequacy_claim": False,
        "canonical_toe_claim": False,
        "master_action_promotion_authorized": False,
        "qft_gr_source_map_closure_authorized": False,
        "governance_manifest_enrollment_authorized": False,
    }
    assert report["next_target_expectations"] == {
        "target_id": SELECTED_TARGET,
        "selected_assumption_class_id": SELECTED_CANDIDATE,
        "should_prepare_bounded_reduction_only": True,
        "must_not_claim_entropy_semantics_theorem_discharge": True,
        "must_preserve_supplied_only_qm_stat_entropy_semantics_boundary": True,
    }
    assert report["next_action_after_selection_packet"] == SELECTED_TARGET
    assert "evaluates all 8 mapped supporting assumptions" in report["acceptance_condition"]


def test_qm_stat_entropy_assumption_reduction_candidate_selection_registry_rotates_to_attack() -> None:
    assert_current_target_consistent()
    assert_forbidden_promotions_closed()

    payload = loop_registry()
    state = payload["current_target_state"]
    is_current = assert_historical_target_recorded(
        payload=payload,
        previous_target=CONSUMED_TARGET,
        live_target=SELECTED_TARGET,
        evidence=SELECTION_EVIDENCE,
        lane=ACTIVE_LANE,
    )

    if is_current:
        assert_frontier_matches_registry()
        assert_public_surfaces_match_registry()
        assert state["previous_live_next_target"] == CONSUMED_TARGET
        assert state["live_next_target"] == SELECTED_TARGET
        assert state["live_next_target_evidence"] == SELECTION_EVIDENCE
        assert state["active_lane"] == ACTIVE_LANE
    else:
        assert state["live_next_target"] in {
            "execute_qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_attempt",
            "prepare_qm_stat_entropy_assumption_reduction_candidate_selection",
            "select_next_post_v01_alpha_manifest_enrollment_bounded_attack",
            "review_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_result",
            "review_v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt_result",
            "prepare_v01_alpha_retained_tranche_004_source_map_witness_chain_construction_packet_from_research_candidate",
            "review_v01_alpha_retained_tranche_004_source_map_witness_chain_construction_packet_from_research_candidate_result",
            "execute_v01_alpha_retained_tranche_004_source_map_witness_chain_construction_from_research_candidate",
            "review_v01_alpha_retained_tranche_004_source_map_witness_chain_construction_from_research_candidate_result",
            "prepare_v01_alpha_retained_tranche_004_source_map_authorization_adjudication_packet",
            "review_v01_alpha_retained_tranche_004_source_map_authorization_adjudication_packet_result",
            "prepare_v01_alpha_retained_tranche_004_source_map_closure_adjudication_packet",
            "review_v01_alpha_retained_tranche_004_source_map_closure_adjudication_packet_result",
            "review_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_packet_result",
            "prepare_qft_gr_operator_domain_assumption_reduction_packet",
            "review_qft_gr_operator_domain_assumption_reduction_packet_result",
            "prepare_qft_gr_selected_operator_action_assumption_reduction_packet",
            "review_qft_gr_selected_operator_action_assumption_reduction_packet_result",
            "execute_qft_gr_selected_operator_action_assumption_reduction_attempt",
            "review_qft_gr_selected_operator_action_assumption_reduction_attempt_result",
            "prepare_qft_gr_candidate_source_domain_membership_assumption_reduction_packet",
            "review_qft_gr_candidate_source_domain_membership_assumption_reduction_packet_result",
            "execute_qft_gr_candidate_source_domain_membership_assumption_reduction_attempt",
            "prepare_qft_gr_renormalization_assumption_reduction_packet",
            "select_next_post_toe_expert_translation_bounded_target",
            "prepare_qft_gr_minimal_working_model_demonstration_packet",
            "review_qft_gr_minimal_working_model_demonstration_packet_result",
            "review_qft_gr_minimal_working_model_construction_attempt_result",
            "analyze_qft_gr_minimal_working_model_candidate_only",
            "review_qft_gr_minimal_working_model_candidate_analysis_result",
            "prepare_qft_gr_minimal_working_model_conservation_test_packet",
            "review_qft_gr_minimal_working_model_conservation_test_packet_result",
            "execute_qft_gr_minimal_working_model_conservation_test_attempt",
        }
        assert state["active_lane"] in {
            "execute_qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_attempt",
            "post_qm_stat_entropy_log_domain_reduction_bounded_attack_selection",
            "v01_alpha_governance_manifest_enrollment_result_review",
            "v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet",
            "v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt",
            "v01_alpha_retained_tranche_004_bounded_source_map_witness_chain_research_attempt_result_review",
            "v01_alpha_retained_tranche_004_source_map_witness_chain_construction_packet_from_research_candidate",
            "v01_alpha_retained_tranche_004_source_map_witness_chain_construction_packet_from_research_candidate_result_review",
            "v01_alpha_retained_tranche_004_source_map_witness_chain_construction_from_research_candidate",
            "v01_alpha_retained_tranche_004_source_map_witness_chain_construction_result_review",
            "v01_alpha_retained_tranche_004_source_map_authorization_adjudication_packet",
            "v01_alpha_retained_tranche_004_source_map_authorization_adjudication_result_review",
            "v01_alpha_retained_tranche_004_source_map_closure_adjudication_packet",
            "v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_packet_preparation",
            "qft_gr_covariant_conservation_assumption_reduction_packet_result_review",
            "qft_gr_operator_domain_assumption_reduction_packet_preparation",
            "qft_gr_operator_domain_assumption_reduction_packet_result_review",
            "qft_gr_selected_operator_action_assumption_reduction_packet_preparation",
            "qft_gr_selected_operator_action_assumption_reduction_packet_result_review",
            "qft_gr_selected_operator_action_assumption_reduction_attempt_execution",
            "qft_gr_selected_operator_action_assumption_reduction_attempt_result_review",
            "qft_gr_candidate_source_domain_membership_assumption_reduction_packet_preparation",
            "qft_gr_candidate_source_domain_membership_assumption_reduction_packet_result_review",
            "qft_gr_operator_domain_assumption_reduction_closeout_packet_preparation",
            "qft_gr_operator_domain_assumption_reduction_closeout_packet_result_review",
            "select_next_post_toe_expert_translation_bounded_target",
            "prepare_qft_gr_minimal_working_model_demonstration_packet",
            "review_qft_gr_minimal_working_model_demonstration_packet_result",
            "review_qft_gr_minimal_working_model_construction_attempt_result",
            "analyze_qft_gr_minimal_working_model_candidate_only",
            "review_qft_gr_minimal_working_model_candidate_analysis_result",
            "prepare_qft_gr_minimal_working_model_conservation_test_packet",
            "review_qft_gr_minimal_working_model_conservation_test_packet_result",
            "execute_qft_gr_minimal_working_model_conservation_test_attempt",
        }
    assert PREVIOUS_LANE in state["paused_lanes"]
    assert ACTIVE_LANE in state["paused_lanes"]

    previous = workstream(PREVIOUS_LANE, payload)
    assert previous["status"] == "paused"
    assert previous["authorized_next_strict_target"] == CONSUMED_TARGET
    assert previous["output_token"] == CONSUMED_SELECTOR_TOKEN
    assert previous["selected_next_target"] == CONSUMED_TARGET
    assert previous["dependency_map_only"] == "yes"
    assert previous["assumption_class_count"] == 8
    assert previous["selection_executes_target"] == "no"
    assert previous["theorem_gap_discharged"] == "no"

    current = workstream(ACTIVE_LANE, payload)
    assert current["workstream_id"] == ACTIVE_LANE
    assert current["status"] == "paused"
    assert current["authorization_evidence"] == SELECTION_EVIDENCE
    assert current["authorized_next_strict_target"] == SELECTED_TARGET
    assert current["consumed_target"] == CONSUMED_TARGET
    assert current["latest_surface"] == SURFACE_ID
    assert current["selection_report"] == REPORT_EVIDENCE
    assert current["consumed_selector_token"] == CONSUMED_SELECTOR_TOKEN
    assert current["result_token"] == RESULT_TOKEN
    assert current["selected_assumption_class_id"] == SELECTED_CANDIDATE
    assert current["selected_next_target"] == SELECTED_TARGET
    assert current["selection_count"] == 1
    assert current["assumption_class_count"] == 8
    assert current["selection_criteria_count"] == 5
    assert current["reduction_executed"] == "no"
    assert current["assumption_discharge_claim"] == "no"
    assert current["target_stat_entropy_semantics_lean_backed"] == "no"
    assert current["target_stat_entropy_semantics_supplied_only"] == "yes"
    assert current["theorem_gap_discharged"] == "no"
    assert current["qm_stat_pillar_completion_inferred"] == "no"
    assert current["qft_gr_source_map_closure_authorized"] == "no"
    assert current["seam_closure_claim"] == "no"
    assert current["phase2_readiness_claim"] == "no"
    assert current["empirical_adequacy_claim"] == "no"
    assert current["canonical_toe_claim"] == "no"
    assert current["governance_manifest_enrollment_authorized"] == "no"
    assert current["master_action_promotion_authorized"] == "no"

    assert SELECTED_TARGET in payload["next_strict_target_coverage"]
    assert (
        "qm_stat_entropy_assumption_reduction_candidate_selection_nonclaim_boundary"
        in payload["retained_blocker_coverage"]
    )


def test_qm_stat_entropy_assumption_reduction_candidate_selection_public_surfaces_are_synchronized() -> None:
    for path in {
        README_PATH,
        STATE_PATH,
        STRICT_MAP_PATH,
        CURRENT_AUTHORITATIVE_SURFACES_PATH,
    }:
        text = _read(path)
        for token in {
            RESULT_TOKEN,
            SELECTED_CANDIDATE,
            "all eight",
            "supplied-only",
        }:
            assert token in text

    assert_public_surfaces_match_registry()
    assert_frontier_matches_registry()
    assert_forbidden_promotions_closed()


def test_qm_stat_entropy_assumption_reduction_candidate_selection_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_qm_stat_entropy_assumption_reduction_candidate_selection_gate.py"
    )
