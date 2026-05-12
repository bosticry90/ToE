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
    assert_public_surfaces_match_registry,
    loop_registry,
    workstream,
)


REPO_ROOT = find_repo_root(Path(__file__))
SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "FullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGap.lean"
)
POST_QM_STAT_SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostQMStatEntropySemanticsGapBoundedAttackSelection.lean"
)
TARGET_MAP_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "FullPillarTargetMapRebase.lean"
)
AGGREGATE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_AFTER_QM_STAT_ENTROPY_SEMANTICS_GAP_20260510_v0.json"
)
POST_QM_STAT_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "POST_QM_STAT_ENTROPY_SEMANTICS_GAP_BOUNDED_ATTACK_SELECTION_20260510_v0.json"
)

REPORT_ID = (
    "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_AFTER_QM_STAT_ENTROPY_SEMANTICS_GAP_20260510_v0"
)
SURFACE_ID = (
    "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_v0"
)
ACTIVE_LANE = "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap"
PREVIOUS_LANE = "post_qm_stat_entropy_semantics_gap_bounded_attack_selection"
CONSUMED_TARGET = "return_to_full_pillar_target_map_next_lane_selection"
CONSUMED_TOKEN = "POST_QM_STAT_ENTROPY_SEMANTICS_GAP_NEXT_ATTACK_SELECTED"
RESULT_TOKEN = "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTED_AFTER_QM_STAT_ENTROPY_SEMANTICS_GAP"
SELECTED_LANE = "QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP"
SELECTED_TARGET = "prepare_qm_stat_entropy_semantics_supporting_assumption_map"
SELECTED_KIND = "qm_stat_entropy_semantics_supporting_assumption_map_preparation_only"
SELECTED_GAP = "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_THEOREM_GAP_v0"
SUPPLIED_ONLY_TOKEN = "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_SUPPLIED_ONLY"
REVIEW_TOKEN = (
    "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_THEOREM_GAP_RESULT_REVIEW_CONSUMED_SUPPLIED_ONLY"
)
CANDIDATE_CLASSES = {
    "NEXT_PROOF_DEBT_LEDGER_DISCHARGE_ITEM",
    SELECTED_LANE,
    "SR_COSMO_GLOBAL_OBSTRUCTION_FOLLOW_UP",
    "GR_WEAK_FIELD_SOURCE_SIDE_OBLIGATION_LANE",
    "MASTER_ACTION_DEPENDENCY_GAP_REDUCTION_PLAN",
    "QFT_GR_WITNESS_SEARCH_PLAN",
    "ARTIFACT_RETENTION_MIGRATION_PLAN",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def test_after_qm_stat_entropy_gap_full_pillar_selector_selects_assumption_map() -> None:
    text = _read(SELECTION_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        CONSUMED_TOKEN,
        RESULT_TOKEN,
        SELECTED_LANE,
        SELECTED_TARGET,
        "FullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapStatus",
        "FullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGapDecision",
        "selectQMSTATEntropySemanticsSupportingAssumptionMap",
        "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_consumes_return_target_v0",
        "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_consumes_selector_token_v0",
        "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_rows_evaluated_v0",
        "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_supplied_only_preserved_v0",
        "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_exactly_one_lane_v0",
        "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_result_token_v0",
        "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_selected_lane_v0",
        "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_selected_target_v0",
        "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_decision_v0",
        "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_candidate_count_v0",
    } | CANDIDATE_CLASSES:
        assert token in text

    assert (
        "import ToeFormal.Derivation.FullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGap"
        in aggregate_text
    )


def test_after_qm_stat_entropy_gap_full_pillar_selector_preserves_nonclaims() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_frontier_target_v0",
        "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_does_not_execute_lane_v0",
        "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_no_lean_backed_discharge_v0",
        "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_no_gap_closure_v0",
        "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_qm_stat_supporting_map_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_proof_debt_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_sr_cosmo_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_gr_weak_field_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_qft_gr_witness_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_gap_reduction_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_artifact_migration_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_no_qm_stat_completion_v0",
        "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_no_seam_closure_v0",
        "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_no_phase2_readiness_v0",
        "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_no_empirical_adequacy_v0",
        "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_no_canonical_toe_claim_v0",
        "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_master_action_not_promoted_v0",
        "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_qft_gr_not_authorized_v0",
        "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_manifest_not_enrolled_v0",
    }:
        assert token in text


def test_after_qm_stat_entropy_gap_full_pillar_report_records_selected_lane() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["selection_status"] == "completed_selection_only"
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_selector_token"] == CONSUMED_TOKEN
    assert report["result_token"] == RESULT_TOKEN
    assert report["selected_lane"] == SELECTED_LANE
    assert report["selected_next_target"] == SELECTED_TARGET
    assert report["selected_next_target_kind"] == SELECTED_KIND
    assert report["selection_surface"] == _rel(SELECTION_PATH)
    assert report["post_qm_stat_entropy_semantics_gap_selection_surface"] == _rel(
        POST_QM_STAT_SELECTION_PATH
    )
    assert report["post_qm_stat_entropy_semantics_gap_selection_report"] == _rel(
        POST_QM_STAT_REPORT_PATH
    )
    assert report["target_map_surface"] == _rel(TARGET_MAP_PATH)
    assert report["authorized_effect"] == "SELECT_EXACTLY_ONE_NEXT_BOUNDED_LANE"
    assert report["selection_executes_lane"] is False
    assert report["selection_count"] == 1
    assert report["candidate_lane_count"] == 7

    selected = [row for row in report["candidate_classes"] if row["selection"] == "selected"]
    assert len(selected) == 1
    assert selected[0]["class_id"] == SELECTED_LANE
    assert selected[0]["candidate_target"] == SELECTED_TARGET
    assert {row["class_id"] for row in report["candidate_classes"]} == CANDIDATE_CLASSES
    assert report["next_action_after_selection_packet"] == SELECTED_TARGET


def test_after_qm_stat_entropy_gap_full_pillar_report_preserves_boundaries() -> None:
    report = _json(REPORT_PATH)

    assert report["qm_stat_supplied_only_basis"] == {
        "selected_gap": SELECTED_GAP,
        "source_result_token": SUPPLIED_ONLY_TOKEN,
        "source_review_token": REVIEW_TOKEN,
        "target_stat_entropy_semantics_authority": (
            "SUPPLIED_ONLY_TARGET_STAT_ENTROPY_SEMANTICS_RETAINED"
        ),
        "lean_backed_entropy_semantics_discharge": False,
        "theorem_gap_discharged": False,
    }
    assert report["nonclaim_boundaries"] == {
        "selection_executes_lane": False,
        "target_stat_entropy_semantics_lean_backed": False,
        "target_stat_entropy_semantics_supplied_only": True,
        "theorem_gap_discharged": False,
        "proof_debt_discharge_item_selected": False,
        "qm_stat_supporting_assumption_map_selected": True,
        "sr_cosmo_obstruction_followup_selected": False,
        "gr_weak_field_source_side_selected": False,
        "qft_gr_witness_search_selected": False,
        "master_action_gap_reduction_selected": False,
        "artifact_retention_migration_plan_selected": False,
        "qm_stat_pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "phase2_readiness_claim": False,
        "empirical_adequacy_claim": False,
        "canonical_toe_claim": False,
        "master_action_promotion_authorized": False,
        "qft_gr_source_map_closure_authorized": False,
        "governance_manifest_enrollment_authorized": False,
    }


def test_after_qm_stat_entropy_gap_full_pillar_registry_rotates_to_supporting_map() -> None:
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()
    assert_forbidden_promotions_closed()

    payload = loop_registry()
    state = payload["current_target_state"]

    assert SELECTED_TARGET in payload["next_strict_target_coverage"]
    assert state["live_next_target"] != SELECTED_TARGET
    assert ACTIVE_LANE in state["paused_lanes"]
    assert PREVIOUS_LANE in state["paused_lanes"]

    previous = workstream(PREVIOUS_LANE, payload)
    assert previous["status"] == "paused"
    assert previous["authorized_next_strict_target"] == CONSUMED_TARGET
    assert previous["output_token"] == CONSUMED_TOKEN
    assert previous["selected_next_target"] == CONSUMED_TARGET
    assert previous["target_stat_entropy_semantics_supplied_only"] == "yes"

    current = workstream(ACTIVE_LANE, payload)
    assert current["status"] == "paused"
    assert current["authorization_evidence"] == _rel(SELECTION_PATH)
    assert current["authorized_next_strict_target"] == SELECTED_TARGET
    assert current["consumed_target"] == CONSUMED_TARGET
    assert current["latest_surface"] == SURFACE_ID
    assert current["selector_report"] == _rel(REPORT_PATH)
    assert current["consumed_selector_token"] == CONSUMED_TOKEN
    assert current["result_token"] == RESULT_TOKEN
    assert current["selected_lane"] == SELECTED_LANE
    assert current["selected_next_target"] == SELECTED_TARGET
    assert current["selected_next_target_kind"] == SELECTED_KIND
    assert current["selection_executes_lane"] == "no"
    assert current["target_stat_entropy_semantics_supplied_only"] == "yes"
    assert current["target_stat_entropy_semantics_lean_backed"] == "no"
    assert current["theorem_gap_discharged"] == "no"
    assert current["qm_stat_supporting_assumption_map_selected"] == "yes"
    assert current["qm_stat_pillar_completion_inferred"] == "no"
    assert current["qft_gr_source_map_closure_authorized"] == "no"
    assert current["seam_closure_claim"] == "no"
    assert current["phase2_readiness_claim"] == "no"
    assert current["empirical_adequacy_claim"] == "no"
    assert current["canonical_toe_claim"] == "no"
    assert current["governance_manifest_enrollment_authorized"] == "no"
    assert current["master_action_promotion_authorized"] == "no"


def test_after_qm_stat_entropy_gap_full_pillar_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap_gate.py"
    )
