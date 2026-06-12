from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_current_target_consistent,
    assert_focused_gate_not_manifest_enrolled,
    assert_forbidden_promotions_closed,
    assert_frontier_matches_registry,
    assert_historical_target_recorded,
    assert_public_surfaces_match_registry,
    loop_registry,
    workstream,
)


REPO_ROOT = find_repo_root(Path(__file__))
REVIEW_SURFACE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMStatEntropySemanticsSupportingAssumptionMapResultReview.lean"
)
MAP_SURFACE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMStatEntropySemanticsSupportingAssumptionMap.lean"
)
FULL_PILLAR_SELECTOR_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "FullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGap.lean"
)
AGGREGATE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP_RESULT_REVIEW_20260510_v0.json"
)
MAP_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP_20260510_v0.json"
)

REPORT_ID = (
    "QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP_RESULT_REVIEW_20260510_v0"
)
SURFACE_ID = "qm_stat_entropy_semantics_supporting_assumption_map_result_review_v0"
CONSUMED_TARGET = "review_qm_stat_entropy_semantics_supporting_assumption_map_result"
CONSUMED_RESULT_TOKEN = "QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP_PREPARED"
REVIEW_TOKEN = "QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP_RESULT_REVIEW_CONSUMED"
NEXT_TARGET = "select_next_post_qm_stat_entropy_assumption_map_bounded_attack"
POST_MAP_SELECTOR_LANE = "post_qm_stat_entropy_assumption_map_bounded_attack_selection"
CANDIDATE_SELECTION_TARGET = (
    "prepare_qm_stat_entropy_assumption_reduction_candidate_selection"
)
CANDIDATE_SELECTION_LANE = "qm_stat_entropy_assumption_reduction_candidate_selection"
NEXT_TARGET_AFTER_CANDIDATE_SELECTION = (
    "prepare_selected_qm_stat_entropy_assumption_reduction_bounded_attack"
)
MAP_TARGET = "prepare_qm_stat_entropy_semantics_supporting_assumption_map"
FULL_PILLAR_TARGET = "return_to_full_pillar_target_map_next_lane_selection"
SELECTED_LANE = "QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP"
SELECTED_GAP = "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_THEOREM_GAP_v0"
SELECTED_OBLIGATION = "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_OBLIGATION_v0"
MAP_LANE = "qm_stat_entropy_semantics_supporting_assumption_map"
REVIEW_LANE = "qm_stat_entropy_semantics_supporting_assumption_map_result_review"
FULL_PILLAR_LANE = (
    "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap"
)
EXPECTED_ASSUMPTION_CLASSES = {
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
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def test_qm_stat_entropy_semantics_supporting_assumption_map_result_review_surface_consumes_map() -> None:
    text = _read(REVIEW_SURFACE_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        CONSUMED_RESULT_TOKEN,
        REVIEW_TOKEN,
        NEXT_TARGET,
        SELECTED_GAP,
        SELECTED_OBLIGATION,
        "consumeDependencyMapAndSelectPostMapBoundedAttack",
        "QMStatEntropySemanticsSupportingAssumptionMapResultReviewStatus",
        "qm_stat_entropy_semantics_supporting_assumption_map_result_review_consumes_live_target_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_result_review_consumes_map_token_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_result_review_token_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_result_review_next_target_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_result_review_rows_preserved_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_result_review_dependency_map_only_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_result_review_supplied_only_preserved_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_result_review_frontier_target_v0",
    } | EXPECTED_ASSUMPTION_CLASSES:
        assert token in text

    assert (
        "import ToeFormal.Derivation.QMStatEntropySemanticsSupportingAssumptionMapResultReview"
        in aggregate_text
    )


def test_qm_stat_entropy_semantics_supporting_assumption_map_result_review_surface_preserves_nonclaims() -> None:
    text = _read(REVIEW_SURFACE_PATH)

    for token in {
        "qm_stat_entropy_semantics_supporting_assumption_map_result_review_does_not_attempt_discharge_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_result_review_no_lean_backed_discharge_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_result_review_no_gap_closure_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_result_review_no_qm_stat_completion_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_result_review_no_seam_closure_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_result_review_no_phase2_readiness_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_result_review_no_empirical_adequacy_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_result_review_no_canonical_toe_claim_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_result_review_master_action_not_promoted_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_result_review_qft_gr_not_authorized_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_result_review_manifest_not_enrolled_v0",
    }:
        assert token in text


def test_qm_stat_entropy_semantics_supporting_assumption_map_result_review_report_records_review() -> None:
    report = _json(REPORT_PATH)
    source_report = _json(MAP_REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_result_token"] == CONSUMED_RESULT_TOKEN
    assert report["review_token"] == REVIEW_TOKEN
    assert report["source_map_surface"] == _rel(MAP_SURFACE_PATH)
    assert report["source_map_report"] == _rel(MAP_REPORT_PATH)
    assert report["review_surface"] == _rel(REVIEW_SURFACE_PATH)
    assert report["selected_gap"] == SELECTED_GAP
    assert report["selected_obligation"] == SELECTED_OBLIGATION
    assert report["selected_next_target"] == NEXT_TARGET
    assert report["selected_decision"] == (
        "consume_dependency_map_and_select_post_map_bounded_attack"
    )
    assert report["review_interpretation"] == (
        "supporting_assumption_map_consumed_as_dependency_map_only"
    )
    assert report["review_effect"] == {
        "supporting_assumption_map_result_consumed": True,
        "dependency_map_only": True,
        "assumption_class_count": 8,
        "allowed_authority_classification_count": 5,
        "target_stat_entropy_semantics_supplied_only": True,
        "target_stat_entropy_semantics_lean_backed": False,
        "theorem_gap_discharged": False,
    }
    assert set(report["assumption_classes_preserved"]) == EXPECTED_ASSUMPTION_CLASSES
    assert report["authority_summary_preserved"] == source_report["authority_summary"]
    assert report["nonclaim_boundaries"] == {
        "map_attempts_theorem_discharge": False,
        "lean_backed_entropy_semantics_discharge": False,
        "theorem_gap_closure_claim": False,
        "qm_stat_pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "phase2_readiness_claim": False,
        "empirical_adequacy_claim": False,
        "canonical_toe_claim": False,
        "master_action_promotion_authorized": False,
        "qft_gr_source_map_closure_authorized": False,
        "governance_manifest_enrollment_authorized": False,
    }
    assert report["next_action"] == NEXT_TARGET
    assert (
        "all 8 required assumption classes remain recorded"
        in report["acceptance_condition"]
    )


def test_qm_stat_entropy_semantics_supporting_assumption_map_result_review_rotates_current_target() -> None:
    assert_current_target_consistent()
    assert_forbidden_promotions_closed()

    payload = loop_registry()
    state = payload["current_target_state"]
    is_current = assert_historical_target_recorded(
        payload=payload,
        previous_target=CANDIDATE_SELECTION_TARGET,
        live_target=NEXT_TARGET_AFTER_CANDIDATE_SELECTION,
        lane=CANDIDATE_SELECTION_LANE,
    )

    if is_current:
        assert_frontier_matches_registry()
        assert_public_surfaces_match_registry()
        assert state["previous_live_next_target"] == CANDIDATE_SELECTION_TARGET
        assert state["live_next_target"] == NEXT_TARGET_AFTER_CANDIDATE_SELECTION
        assert state["active_lane"] == CANDIDATE_SELECTION_LANE
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
        }
    assert POST_MAP_SELECTOR_LANE in state["paused_lanes"]
    assert CANDIDATE_SELECTION_LANE in state["paused_lanes"]
    assert MAP_LANE in state["paused_lanes"]
    assert REVIEW_LANE in state["paused_lanes"]
    assert FULL_PILLAR_LANE in state["paused_lanes"]

    full_pillar = workstream(FULL_PILLAR_LANE, payload)
    assert full_pillar["status"] == "paused"
    assert full_pillar["authorized_next_strict_target"] == MAP_TARGET
    assert full_pillar["selected_lane"] == SELECTED_LANE
    assert full_pillar["selected_next_target"] == MAP_TARGET
    assert full_pillar["selection_executes_lane"] == "no"
    assert full_pillar["governance_manifest_enrollment_authorized"] == "no"

    source_map = workstream(MAP_LANE, payload)
    assert source_map["status"] == "paused"
    assert source_map["authorization_evidence"] == _rel(MAP_SURFACE_PATH)
    assert source_map["authorized_next_strict_target"] == CONSUMED_TARGET
    assert source_map["consumed_target"] == MAP_TARGET
    assert source_map["result_token"] == CONSUMED_RESULT_TOKEN
    assert source_map["selected_next_target"] == CONSUMED_TARGET
    assert source_map["assumption_class_count"] == 8
    assert source_map["map_attempts_theorem_discharge"] == "no"
    assert source_map["target_stat_entropy_semantics_supplied_only"] == "yes"
    assert source_map["theorem_gap_discharged"] == "no"
    assert source_map["governance_manifest_enrollment_authorized"] == "no"

    review = workstream(REVIEW_LANE, payload)
    assert review["status"] == "paused"
    assert review["authorization_evidence"] == _rel(REVIEW_SURFACE_PATH)
    assert review["authorized_next_strict_target"] == NEXT_TARGET
    assert review["consumed_target"] == CONSUMED_TARGET
    assert review["consumed_result_token"] == CONSUMED_RESULT_TOKEN
    assert review["review_token"] == REVIEW_TOKEN
    assert review["selected_gap"] == SELECTED_GAP
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["assumption_class_count"] == 8
    assert review["dependency_map_only"] == "yes"
    assert review["target_stat_entropy_semantics_supplied_only"] == "yes"
    assert review["target_stat_entropy_semantics_lean_backed"] == "no"
    assert review["theorem_gap_discharged"] == "no"
    assert review["governance_manifest_enrollment_authorized"] == "no"


def test_qm_stat_entropy_semantics_supporting_assumption_map_result_review_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_qm_stat_entropy_semantics_supporting_assumption_map_result_review_gate.py"
    )
