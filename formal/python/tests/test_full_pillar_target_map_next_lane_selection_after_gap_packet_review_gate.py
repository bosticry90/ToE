from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
)


REPO_ROOT = find_repo_root(Path(__file__))
SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "FullPillarTargetMapNextLaneSelectionAfterGapPacketReview.lean"
)
POST_GAP_SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostMasterActionGapPacketBoundedAttackSelection.lean"
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
    / "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_AFTER_GAP_PACKET_REVIEW_20260505_v0.json"
)
POST_GAP_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "POST_MASTER_ACTION_GAP_PACKET_BOUNDED_ATTACK_SELECTION_20260505_v0.json"
)

REPORT_ID = "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_AFTER_GAP_PACKET_REVIEW_20260505_v0"
SURFACE_ID = "full_pillar_target_map_next_lane_selection_after_gap_packet_review_v0"
CONSUMED_TARGET = "return_to_full_pillar_target_map_next_lane_selection"
CONSUMED_TOKEN = "POST_MASTER_ACTION_GAP_PACKET_NEXT_ATTACK_SELECTED"
RESULT_TOKEN = "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTED_AFTER_GAP_PACKET_REVIEW"
SELECTED_LANE = "READ_ONLY_VALIDATION_HYGIENE"
SELECTED_TARGET = "prepare_read_only_validation_hygiene_packet"
CANDIDATE_CLASSES = {
    "PROOF_DEBT_LEDGER_DISCHARGE_LANE",
    "QM_STAT_THEOREM_GAP_RE_ENTRY_LANE",
    "SR_COSMO_GLOBAL_OBSTRUCTION_FOLLOW_UP",
    "QFT_GR_WITNESS_SEARCH_PLAN",
    "MASTER_ACTION_DEPENDENCY_GAP_REDUCTION_PLAN",
    "REPOSITORY_ARTIFACT_RETENTION_POLICY",
    "READ_ONLY_VALIDATION_HYGIENE",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def test_after_gap_full_pillar_selector_selects_read_only_hygiene() -> None:
    text = _read(SELECTION_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        CONSUMED_TOKEN,
        RESULT_TOKEN,
        SELECTED_LANE,
        SELECTED_TARGET,
        "FullPillarTargetMapNextLaneSelectionAfterGapPacketReviewStatus",
        "FullPillarTargetMapNextLaneSelectionAfterGapPacketReviewDecision",
        "selectReadOnlyValidationHygiene",
        "full_pillar_target_map_next_lane_selection_after_gap_packet_review_consumes_return_target_v0",
        "full_pillar_target_map_next_lane_selection_after_gap_packet_review_consumes_selector_token_v0",
        "full_pillar_target_map_next_lane_selection_after_gap_packet_review_rows_evaluated_v0",
        "full_pillar_target_map_next_lane_selection_after_gap_packet_review_read_only_risk_identified_v0",
        "full_pillar_target_map_next_lane_selection_after_gap_packet_review_exactly_one_lane_v0",
        "full_pillar_target_map_next_lane_selection_after_gap_packet_review_result_token_v0",
        "full_pillar_target_map_next_lane_selection_after_gap_packet_review_selected_lane_v0",
        "full_pillar_target_map_next_lane_selection_after_gap_packet_review_selected_target_v0",
        "full_pillar_target_map_next_lane_selection_after_gap_packet_review_candidate_count_v0",
    } | CANDIDATE_CLASSES:
        assert token in text

    assert (
        "import ToeFormal.Derivation.FullPillarTargetMapNextLaneSelectionAfterGapPacketReview"
        in aggregate_text
    )


def test_after_gap_full_pillar_selector_preserves_nonclaims() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        "full_pillar_target_map_next_lane_selection_after_gap_packet_review_axiom_count_v0",
        "full_pillar_target_map_next_lane_selection_after_gap_packet_review_default_nonalias_absent_v0",
        "full_pillar_target_map_next_lane_selection_after_gap_packet_review_sample_rep32_retained_v0",
        "full_pillar_target_map_next_lane_selection_after_gap_packet_review_qft_gr_source_map_not_authorized_v0",
        "full_pillar_target_map_next_lane_selection_after_gap_packet_review_does_not_execute_lane_v0",
        "full_pillar_target_map_next_lane_selection_after_gap_packet_review_proof_debt_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_gap_packet_review_qft_gr_witness_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_gap_packet_review_gap_reduction_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_gap_packet_review_artifact_policy_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_after_gap_packet_review_master_action_not_promoted_v0",
        "full_pillar_target_map_next_lane_selection_after_gap_packet_review_no_pillar_completion_v0",
        "full_pillar_target_map_next_lane_selection_after_gap_packet_review_no_seam_closure_v0",
        "full_pillar_target_map_next_lane_selection_after_gap_packet_review_no_phase2_readiness_v0",
        "full_pillar_target_map_next_lane_selection_after_gap_packet_review_no_empirical_adequacy_v0",
        "full_pillar_target_map_next_lane_selection_after_gap_packet_review_no_canonical_toe_claim_v0",
        "full_pillar_target_map_next_lane_selection_after_gap_packet_review_manifest_not_enrolled_v0",
    }:
        assert token in text


def test_after_gap_full_pillar_report_records_hygiene_lane() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_selector_token"] == CONSUMED_TOKEN
    assert report["result_token"] == RESULT_TOKEN
    assert report["selected_lane"] == SELECTED_LANE
    assert report["selected_next_target"] == SELECTED_TARGET
    assert report["selection_surface"] == str(SELECTION_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
    assert report["post_gap_selection_surface"] == str(POST_GAP_SELECTION_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
    assert report["post_gap_selection_report"] == str(POST_GAP_REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
    assert report["target_map_surface"] == str(TARGET_MAP_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
    assert report["authorized_effect"] == "SELECT_EXACTLY_ONE_NEXT_BOUNDED_LANE"
    assert report["selection_executes_lane"] is False
    assert report["selection_count"] == 1
    assert report["candidate_lane_count"] == 7

    selected = [row for row in report["candidate_classes"] if row["selection"] == "selected"]
    assert len(selected) == 1
    assert selected[0]["class_id"] == SELECTED_LANE
    assert selected[0]["candidate_target"] == SELECTED_TARGET
    assert {row["class_id"] for row in report["candidate_classes"]} == CANDIDATE_CLASSES
    assert report["preserved_posture"]["real_axiom_count"] == 60
    assert report["preserved_posture"]["qft_gr_source_map_closure_authorized"] is False
    assert report["nonclaim_boundaries"]["master_action_promotion_authorized"] is False
    assert report["next_action_after_selection_packet"] == SELECTED_TARGET


def test_after_gap_full_pillar_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_full_pillar_target_map_next_lane_selection_after_gap_packet_review_gate.py"
    )
