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
REVIEW_SURFACE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMStatTargetStatEntropySemanticsTheoremGapResultReview.lean"
)
ATTACK_SURFACE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMStatTargetStatEntropySemanticsTheoremGap.lean"
)
SELECTION_SURFACE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostQMStatEntropySemanticsGapBoundedAttackSelection.lean"
)
FULL_PILLAR_SELECTION_SURFACE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "FullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGap.lean"
)
AGGREGATE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_THEOREM_GAP_RESULT_REVIEW_20260510_v0.json"
)

REPORT_ID = (
    "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_THEOREM_GAP_RESULT_REVIEW_20260510_v0"
)
SURFACE_ID = "qm_stat_target_stat_entropy_semantics_theorem_gap_result_review_v0"
CONSUMED_TARGET = "review_qm_stat_target_stat_entropy_semantics_theorem_gap_result"
CONSUMED_RESULT_TOKEN = "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_SUPPLIED_ONLY"
REVIEW_TOKEN = (
    "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_THEOREM_GAP_RESULT_REVIEW_CONSUMED_SUPPLIED_ONLY"
)
NEXT_TARGET = "select_next_post_qm_stat_entropy_semantics_gap_bounded_attack"
FULL_PILLAR_TARGET = "return_to_full_pillar_target_map_next_lane_selection"
SUPPORTING_MAP_TARGET = "prepare_qm_stat_entropy_semantics_supporting_assumption_map"
SELECTION_TOKEN = "POST_QM_STAT_ENTROPY_SEMANTICS_GAP_NEXT_ATTACK_SELECTED"
FULL_PILLAR_RESULT_TOKEN = (
    "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTED_AFTER_QM_STAT_ENTROPY_SEMANTICS_GAP"
)
SELECTED_GAP = "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_THEOREM_GAP_v0"
SELECTED_OBLIGATION = "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_OBLIGATION_v0"
RETAINED_BLOCKER = (
    "PHASE1-BLOCKER-QMSTAT-TARGET-STAT-ENTROPY-SEMANTICS-SUPPLIED-ONLY-RETAINED"
)
REVIEW_LANE = "qm_stat_target_stat_entropy_semantics_theorem_gap_result_review"
SELECTION_LANE = "post_qm_stat_entropy_semantics_gap_bounded_attack_selection"
FULL_PILLAR_SELECTION_LANE = (
    "full_pillar_target_map_next_lane_selection_after_qm_stat_entropy_semantics_gap"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def test_qm_stat_target_stat_entropy_semantics_result_review_surface_consumes_supplied_only() -> None:
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
        "consumeSuppliedOnlyAndSelectPostGapBoundedAttack",
        "qm_stat_target_stat_entropy_semantics_result_review_consumes_live_target_v0",
        "qm_stat_target_stat_entropy_semantics_result_review_consumes_supplied_only_token_v0",
        "qm_stat_target_stat_entropy_semantics_result_review_token_v0",
        "qm_stat_target_stat_entropy_semantics_result_review_selected_gap_v0",
        "qm_stat_target_stat_entropy_semantics_result_review_single_gap_scope_v0",
        "qm_stat_target_stat_entropy_semantics_result_review_supplied_only_v0",
        "qm_stat_target_stat_entropy_semantics_result_review_selected_next_target_v0",
        "qm_stat_target_stat_entropy_semantics_result_review_frontier_target_v0",
    }:
        assert token in text

    assert (
        "import ToeFormal.Derivation.QMStatTargetStatEntropySemanticsTheoremGapResultReview"
        in aggregate_text
    )


def test_qm_stat_target_stat_entropy_semantics_result_review_preserves_nonclaims() -> None:
    text = _read(REVIEW_SURFACE_PATH)

    for token in {
        "qm_stat_target_stat_entropy_semantics_result_review_no_lean_backed_discharge_v0",
        "qm_stat_target_stat_entropy_semantics_result_review_no_gap_closure_v0",
        "qm_stat_target_stat_entropy_semantics_result_review_no_qm_stat_completion_v0",
        "qm_stat_target_stat_entropy_semantics_result_review_no_seam_closure_v0",
        "qm_stat_target_stat_entropy_semantics_result_review_no_phase2_readiness_v0",
        "qm_stat_target_stat_entropy_semantics_result_review_no_empirical_adequacy_v0",
        "qm_stat_target_stat_entropy_semantics_result_review_no_canonical_toe_claim_v0",
        "qm_stat_target_stat_entropy_semantics_result_review_master_action_not_promoted_v0",
        "qm_stat_target_stat_entropy_semantics_result_review_qft_gr_not_authorized_v0",
        "qm_stat_target_stat_entropy_semantics_result_review_manifest_not_enrolled_v0",
    }:
        assert token in text


def test_qm_stat_target_stat_entropy_semantics_result_review_report_records_review() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_result_token"] == CONSUMED_RESULT_TOKEN
    assert report["review_token"] == REVIEW_TOKEN
    assert report["source_surface"] == _rel(ATTACK_SURFACE_PATH)
    assert report["review_surface"] == _rel(REVIEW_SURFACE_PATH)
    assert report["selected_gap"] == SELECTED_GAP
    assert report["selected_obligation"] == SELECTED_OBLIGATION
    assert report["selected_gap_count"] == 1
    assert report["selected_next_target"] == NEXT_TARGET
    assert report["selected_decision"] == (
        "consume_supplied_only_and_select_post_gap_bounded_attack"
    )
    assert report["result_interpretation"] == (
        "target_stat_entropy_semantics_remain_supplied_only_under_current_authority"
    )
    assert report["retained_blocker"] == RETAINED_BLOCKER
    assert report["review_effect"] == {
        "supplied_only_result_consumed": True,
        "single_gap_scope_preserved": True,
        "target_stat_entropy_semantics_supplied_only": True,
        "target_stat_entropy_semantics_lean_backed": False,
        "theorem_gap_discharged": False,
    }
    assert not any(report["nonclaim_boundaries"].values())
    assert report["next_action"] == NEXT_TARGET


def test_qm_stat_target_stat_entropy_semantics_result_review_rotates_to_selector() -> None:
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_forbidden_promotions_closed()
    assert_public_surfaces_match_registry()

    payload = loop_registry()
    state = payload["current_target_state"]

    assert state["previous_live_next_target"] == FULL_PILLAR_TARGET
    assert state["live_next_target"] == SUPPORTING_MAP_TARGET
    assert state["live_next_target_evidence"] == _rel(FULL_PILLAR_SELECTION_SURFACE_PATH)
    assert state["active_lane"] == FULL_PILLAR_SELECTION_LANE
    assert REVIEW_LANE in state["paused_lanes"]
    assert SELECTION_LANE in state["paused_lanes"]

    review = workstream(REVIEW_LANE, payload)
    assert review["status"] == "paused"
    assert review["authorized_next_strict_target"] == NEXT_TARGET
    assert review["consumed_target"] == CONSUMED_TARGET
    assert review["consumed_result_token"] == CONSUMED_RESULT_TOKEN
    assert review["review_token"] == REVIEW_TOKEN
    assert review["selected_gap"] == SELECTED_GAP
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["target_stat_entropy_semantics_supplied_only"] == "yes"
    assert review["target_stat_entropy_semantics_lean_backed"] == "no"
    assert review["theorem_gap_discharged"] == "no"
    assert review["governance_manifest_enrollment_authorized"] == "no"

    selector = workstream(SELECTION_LANE, payload)
    assert selector["status"] == "paused"
    assert selector["authorization_evidence"] == _rel(SELECTION_SURFACE_PATH)
    assert selector["authorized_next_strict_target"] == FULL_PILLAR_TARGET
    assert selector["consumed_target"] == NEXT_TARGET
    assert selector["consumed_review_token"] == REVIEW_TOKEN
    assert selector["output_token"] == SELECTION_TOKEN
    assert selector["selected_next_target"] == FULL_PILLAR_TARGET
    assert selector["selection_executes_target"] == "no"
    assert selector["governance_manifest_enrollment_authorized"] == "no"

    full_pillar_selector = workstream(FULL_PILLAR_SELECTION_LANE, payload)
    assert full_pillar_selector["status"] == "active"
    assert full_pillar_selector["authorization_evidence"] == _rel(
        FULL_PILLAR_SELECTION_SURFACE_PATH
    )
    assert full_pillar_selector["authorized_next_strict_target"] == SUPPORTING_MAP_TARGET
    assert full_pillar_selector["consumed_target"] == FULL_PILLAR_TARGET
    assert full_pillar_selector["consumed_selector_token"] == SELECTION_TOKEN
    assert full_pillar_selector["result_token"] == FULL_PILLAR_RESULT_TOKEN
    assert (
        full_pillar_selector["selected_lane"]
        == "QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP"
    )
    assert full_pillar_selector["selected_next_target"] == SUPPORTING_MAP_TARGET
    assert full_pillar_selector["selection_executes_lane"] == "no"
    assert full_pillar_selector["target_stat_entropy_semantics_supplied_only"] == "yes"
    assert full_pillar_selector["theorem_gap_discharged"] == "no"
    assert full_pillar_selector["governance_manifest_enrollment_authorized"] == "no"


def test_qm_stat_target_stat_entropy_semantics_result_review_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_qm_stat_target_stat_entropy_semantics_theorem_gap_result_review_gate.py"
    )
