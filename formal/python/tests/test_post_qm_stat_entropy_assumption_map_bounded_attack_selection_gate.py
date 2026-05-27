from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.tests.strict_physics_state_helpers import (
    README_PATH,
    REPO_ROOT,
    STATE_PATH,
    STRICT_MAP_PATH,
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


SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostQMStatEntropyAssumptionMapBoundedAttackSelection.lean"
)
REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMStatEntropySemanticsSupportingAssumptionMapResultReview.lean"
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
    / "POST_QM_STAT_ENTROPY_ASSUMPTION_MAP_BOUNDED_ATTACK_SELECTION_20260510_v0.json"
)
REVIEW_REPORT_PATH = (
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
CURRENT_AUTHORITATIVE_SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)

REPORT_ID = "POST_QM_STAT_ENTROPY_ASSUMPTION_MAP_BOUNDED_ATTACK_SELECTION_20260510_v0"
SURFACE_ID = "post_qm_stat_entropy_assumption_map_bounded_attack_selection_v0"
ACTIVE_LANE = "post_qm_stat_entropy_assumption_map_bounded_attack_selection"
CANDIDATE_SELECTION_LANE = "qm_stat_entropy_assumption_reduction_candidate_selection"
PREVIOUS_LANE = "qm_stat_entropy_semantics_supporting_assumption_map_result_review"
SELECTION_TARGET = "select_next_post_qm_stat_entropy_assumption_map_bounded_attack"
CONSUMED_REVIEW_TARGET = "review_qm_stat_entropy_semantics_supporting_assumption_map_result"
CONSUMED_REVIEW_TOKEN = (
    "QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP_RESULT_REVIEW_CONSUMED"
)
OUTPUT_TOKEN = "POST_QM_STAT_ENTROPY_ASSUMPTION_MAP_NEXT_ATTACK_SELECTED"
SELECTED_TARGET = "prepare_qm_stat_entropy_assumption_reduction_candidate_selection"
NEXT_TARGET_AFTER_CANDIDATE_SELECTION = (
    "prepare_selected_qm_stat_entropy_assumption_reduction_bounded_attack"
)
ALTERNATE_TARGET = "return_to_full_pillar_target_map_next_lane_selection"
SELECTED_GAP = "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_THEOREM_GAP_v0"
SELECTED_OBLIGATION = "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_OBLIGATION_v0"
SELECTION_EVIDENCE = str(SELECTION_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REVIEW_EVIDENCE = str(REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
MAP_EVIDENCE = str(MAP_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REVIEW_REPORT_EVIDENCE = str(REVIEW_REPORT_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
MAP_REPORT_EVIDENCE = str(MAP_REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")


def _read(path: Path) -> str:
    return read_text(path)


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def test_post_qm_stat_entropy_assumption_map_selection_surface_records_target() -> None:
    text = _read(SELECTION_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        SELECTION_TARGET,
        CONSUMED_REVIEW_TOKEN,
        OUTPUT_TOKEN,
        SELECTED_TARGET,
        ALTERNATE_TARGET,
        "PostQMStatEntropyAssumptionMapBoundedAttackSelectionStatus",
        "PostQMStatEntropyAssumptionMapBoundedAttackSelectionDecision",
        "prepareQMStatEntropyAssumptionReductionCandidateSelection",
        "post_qm_stat_entropy_assumption_map_selection_consumes_live_target_v0",
        "post_qm_stat_entropy_assumption_map_selection_consumes_review_token_v0",
        "post_qm_stat_entropy_assumption_map_selection_review_consumed_v0",
        "post_qm_stat_entropy_assumption_map_selection_dependency_map_only_v0",
        "post_qm_stat_entropy_assumption_map_selection_assumption_rows_preserved_v0",
        "post_qm_stat_entropy_assumption_map_selection_exactly_one_target_v0",
        "post_qm_stat_entropy_assumption_map_selection_output_token_v0",
        "post_qm_stat_entropy_assumption_map_selection_decision_v0",
        "post_qm_stat_entropy_assumption_map_selection_selected_target_v0",
        "post_qm_stat_entropy_assumption_map_selection_candidate_count_v0",
        "post_qm_stat_entropy_assumption_map_selection_frontier_target_v0",
    }:
        assert token in text

    assert (
        "import ToeFormal.Derivation.PostQMStatEntropyAssumptionMapBoundedAttackSelection"
        in aggregate_text
    )


def test_post_qm_stat_entropy_assumption_map_selection_surface_preserves_nonclaims() -> None:
    text = _read(SELECTION_PATH)

    for theorem in {
        "post_qm_stat_entropy_assumption_map_selection_does_not_execute_target_v0",
        "post_qm_stat_entropy_assumption_map_selection_no_lean_backed_discharge_v0",
        "post_qm_stat_entropy_assumption_map_selection_supplied_only_preserved_v0",
        "post_qm_stat_entropy_assumption_map_selection_no_gap_closure_v0",
        "post_qm_stat_entropy_assumption_map_selection_no_qm_stat_completion_v0",
        "post_qm_stat_entropy_assumption_map_selection_no_seam_closure_v0",
        "post_qm_stat_entropy_assumption_map_selection_no_phase2_readiness_v0",
        "post_qm_stat_entropy_assumption_map_selection_no_empirical_adequacy_v0",
        "post_qm_stat_entropy_assumption_map_selection_no_canonical_toe_claim_v0",
        "post_qm_stat_entropy_assumption_map_selection_master_action_not_promoted_v0",
        "post_qm_stat_entropy_assumption_map_selection_qft_gr_not_authorized_v0",
        "post_qm_stat_entropy_assumption_map_selection_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_post_qm_stat_entropy_assumption_map_selection_report_selects_candidate_selection() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["selection_status"] == "completed_selection_only"
    assert report["current_target"] == SELECTION_TARGET
    assert report["consumed_review_target"] == CONSUMED_REVIEW_TARGET
    assert report["consumed_review_token"] == CONSUMED_REVIEW_TOKEN
    assert report["output_token"] == OUTPUT_TOKEN
    assert report["source_review_surface"] == REVIEW_EVIDENCE
    assert report["source_review_report"] == REVIEW_REPORT_EVIDENCE
    assert report["source_map_surface"] == MAP_EVIDENCE
    assert report["source_map_report"] == MAP_REPORT_EVIDENCE
    assert report["selection_surface"] == SELECTION_EVIDENCE
    assert report["focused_gate"] == (
        "formal/python/tests/test_post_qm_stat_entropy_assumption_map_bounded_attack_selection_gate.py"
    )
    assert report["authorized_effect"] == "SELECT_EXACTLY_ONE_NEXT_BOUNDED_TARGET"
    assert report["selection_executes_target"] is False
    assert report["selection_count"] == 1
    assert report["selected_next_target"] == SELECTED_TARGET
    assert report["selected_decision"] == SELECTED_TARGET

    selected = [
        row for row in report["candidate_next_targets"] if row["selection"] == "selected"
    ]
    assert len(selected) == 1
    assert selected[0]["target_id"] == SELECTED_TARGET
    assert {row["target_id"] for row in report["candidate_next_targets"]} == {
        SELECTED_TARGET,
        ALTERNATE_TARGET,
    }


def test_post_qm_stat_entropy_assumption_map_selection_report_preserves_review_boundary() -> None:
    report = _json(REPORT_PATH)

    assert report["review_interpretation"] == {
        "supporting_assumption_map_result_review_consumed": True,
        "dependency_map_only": True,
        "selected_gap": SELECTED_GAP,
        "selected_obligation": SELECTED_OBLIGATION,
        "assumption_class_count": 8,
        "target_stat_entropy_semantics_authority": (
            "SUPPLIED_ONLY_TARGET_STAT_ENTROPY_SEMANTICS_WITH_EXPLICIT_ASSUMPTION_MAP_RETAINED"
        ),
        "theorem_gap_discharged": False,
    }
    assert report["next_target_expectations"] == {
        "target_id": SELECTED_TARGET,
        "candidate_selection_should_rank_assumptions": True,
        "candidate_selection_should_select_exactly_one_assumption": True,
        "selector_executes_selected_target": False,
        "must_preserve_supplied_only_qm_stat_entropy_semantics_boundary": True,
    }
    assert report["nonclaim_boundaries"] == {
        "dependency_map_only": True,
        "all_8_assumption_classes_recorded": True,
        "target_stat_entropy_semantics_lean_backed": False,
        "target_stat_entropy_semantics_supplied_only": True,
        "theorem_gap_discharged": False,
        "assumption_discharge_claim": False,
        "qm_stat_pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "phase2_readiness_claim": False,
        "empirical_adequacy_claim": False,
        "canonical_toe_claim": False,
        "master_action_promotion_authorized": False,
        "qft_gr_source_map_closure_authorized": False,
        "governance_manifest_enrollment_authorized": False,
    }
    assert report["next_action_after_selection_packet"] == SELECTED_TARGET

    for forbidden in {
        "LEAN_BACKED_ENTROPY_SEMANTICS_DISCHARGE",
        "ASSUMPTION_DISCHARGE",
        "THEOREM_GAP_CLOSURE",
        "QM_STAT_PILLAR_COMPLETION",
        "SEAM_CLOSURE",
        "PHASE_2_READINESS",
        "EMPIRICAL_ADEQUACY",
        "CANONICAL_TOE_STATUS",
        "MASTER_ACTION_PROMOTION",
        "QFT_GR_SOURCE_MAP_CLOSURE",
        "SELECTED_TARGET_EXECUTION",
        "GOVERNANCE_MANIFEST_ENROLLMENT",
    }:
        assert forbidden in report["forbidden_effects"]


def test_post_qm_stat_entropy_assumption_map_selection_registry_rotates_to_candidate_selection() -> None:
    assert_current_target_consistent()
    assert_forbidden_promotions_closed()

    payload = loop_registry()
    state = payload["current_target_state"]
    is_current = assert_historical_target_recorded(
        payload=payload,
        previous_target=SELECTED_TARGET,
        live_target=NEXT_TARGET_AFTER_CANDIDATE_SELECTION,
        lane=CANDIDATE_SELECTION_LANE,
    )

    if is_current:
        assert_frontier_matches_registry()
        assert_public_surfaces_match_registry()
        assert state["previous_live_next_target"] == SELECTED_TARGET
        assert state["live_next_target"] == NEXT_TARGET_AFTER_CANDIDATE_SELECTION
        assert state["active_lane"] == CANDIDATE_SELECTION_LANE
    else:
        assert state["live_next_target"] in {
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
        }
        assert state["active_lane"] in {
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
        }
    assert ACTIVE_LANE in state["paused_lanes"]
    assert PREVIOUS_LANE in state["paused_lanes"]

    previous_workstream = workstream(PREVIOUS_LANE, payload)
    assert previous_workstream["status"] == "paused"
    assert previous_workstream["authorized_next_strict_target"] == SELECTION_TARGET
    assert previous_workstream["review_token"] == CONSUMED_REVIEW_TOKEN
    assert previous_workstream["selected_next_target"] == SELECTION_TARGET
    assert previous_workstream["dependency_map_only"] == "yes"
    assert previous_workstream["assumption_class_count"] == 8
    assert previous_workstream["target_stat_entropy_semantics_supplied_only"] == "yes"
    assert previous_workstream["theorem_gap_discharged"] == "no"

    selector = workstream(ACTIVE_LANE, payload)
    assert selector["status"] == "paused"
    assert selector["authorization_evidence"] == SELECTION_EVIDENCE
    assert selector["authorized_next_strict_target"] == SELECTED_TARGET
    assert selector["consumed_target"] == SELECTION_TARGET
    assert selector["latest_surface"] == SURFACE_ID
    assert selector["selection_report"] == REPORT_EVIDENCE
    assert selector["consumed_review_token"] == CONSUMED_REVIEW_TOKEN
    assert selector["output_token"] == OUTPUT_TOKEN
    assert selector["selected_gap"] == SELECTED_GAP
    assert selector["selected_next_target"] == SELECTED_TARGET
    assert selector["selected_decision"] == SELECTED_TARGET
    assert selector["selection_count"] == 1
    assert selector["candidate_target_count"] == 2
    assert selector["selection_executes_target"] == "no"
    assert selector["dependency_map_only"] == "yes"
    assert selector["assumption_class_count"] == 8
    assert selector["target_stat_entropy_semantics_lean_backed"] == "no"
    assert selector["target_stat_entropy_semantics_supplied_only"] == "yes"
    assert selector["theorem_gap_discharged"] == "no"
    assert selector["assumption_discharge_claim"] == "no"
    assert selector["qm_stat_pillar_completion_inferred"] == "no"
    assert selector["qft_gr_source_map_closure_authorized"] == "no"
    assert selector["seam_closure_claim"] == "no"
    assert selector["phase2_readiness_claim"] == "no"
    assert selector["empirical_adequacy_claim"] == "no"
    assert selector["canonical_toe_claim"] == "no"
    assert selector["governance_manifest_enrollment_authorized"] == "no"
    assert selector["master_action_promotion_authorized"] == "no"

    candidate = workstream(CANDIDATE_SELECTION_LANE, payload)
    assert candidate["workstream_id"] == CANDIDATE_SELECTION_LANE
    assert candidate["status"] == "paused"

    assert SELECTED_TARGET in payload["next_strict_target_coverage"]
    assert (
        "post_qm_stat_entropy_assumption_map_bounded_attack_selection_nonclaim_boundary"
        in payload["retained_blocker_coverage"]
    )


def test_post_qm_stat_entropy_assumption_map_selection_public_surfaces_are_synchronized() -> None:
    for path in {
        README_PATH,
        STATE_PATH,
        STRICT_MAP_PATH,
        CURRENT_AUTHORITATIVE_SURFACES_PATH,
    }:
        text = _read(path)
        for token in {
            OUTPUT_TOKEN,
            CONSUMED_REVIEW_TOKEN,
            "all eight",
            "supplied-only",
        }:
            assert token in text

    assert_public_surfaces_match_registry()
    assert_frontier_matches_registry()
    assert_forbidden_promotions_closed()


def test_post_qm_stat_entropy_assumption_map_selection_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_post_qm_stat_entropy_assumption_map_bounded_attack_selection_gate.py"
    )
