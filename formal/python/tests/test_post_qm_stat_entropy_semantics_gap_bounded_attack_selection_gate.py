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
    / "PostQMStatEntropySemanticsGapBoundedAttackSelection.lean"
)
REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMStatTargetStatEntropySemanticsTheoremGapResultReview.lean"
)
ATTACK_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMStatTargetStatEntropySemanticsTheoremGap.lean"
)
AGGREGATE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "POST_QM_STAT_ENTROPY_SEMANTICS_GAP_BOUNDED_ATTACK_SELECTION_20260510_v0.json"
)
REVIEW_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_THEOREM_GAP_RESULT_REVIEW_20260510_v0.json"
)
ATTACK_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_THEOREM_GAP_BOUNDED_ATTACK_20260510_v0.json"
)
CURRENT_AUTHORITATIVE_SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)

REPORT_ID = "POST_QM_STAT_ENTROPY_SEMANTICS_GAP_BOUNDED_ATTACK_SELECTION_20260510_v0"
SURFACE_ID = "post_qm_stat_entropy_semantics_gap_bounded_attack_selection_v0"
ACTIVE_LANE = "post_qm_stat_entropy_semantics_gap_bounded_attack_selection"
PREVIOUS_WORKSTREAM = "qm_stat_target_stat_entropy_semantics_theorem_gap_result_review"
SELECTION_TARGET = "select_next_post_qm_stat_entropy_semantics_gap_bounded_attack"
CONSUMED_REVIEW_TARGET = "review_qm_stat_target_stat_entropy_semantics_theorem_gap_result"
CONSUMED_REVIEW_TOKEN = (
    "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_THEOREM_GAP_RESULT_REVIEW_CONSUMED_SUPPLIED_ONLY"
)
SUPPLIED_ONLY_TOKEN = "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_SUPPLIED_ONLY"
OUTPUT_TOKEN = "POST_QM_STAT_ENTROPY_SEMANTICS_GAP_NEXT_ATTACK_SELECTED"
SELECTED_TARGET = "return_to_full_pillar_target_map_next_lane_selection"
SUPPORTING_MAP_TARGET = "prepare_qm_stat_entropy_semantics_supporting_assumption_map"
SELECTED_GAP = "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_THEOREM_GAP_v0"
SELECTED_OBLIGATION = "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_OBLIGATION_v0"
SELECTION_EVIDENCE = str(SELECTION_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REVIEW_EVIDENCE = str(REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
ATTACK_EVIDENCE = str(ATTACK_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REVIEW_REPORT_EVIDENCE = str(REVIEW_REPORT_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
ATTACK_REPORT_EVIDENCE = str(ATTACK_REPORT_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)


def _read(path: Path) -> str:
    return read_text(path)


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def test_post_qm_stat_entropy_semantics_gap_selection_surface_records_target() -> None:
    text = _read(SELECTION_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        SELECTION_TARGET,
        CONSUMED_REVIEW_TOKEN,
        OUTPUT_TOKEN,
        SELECTED_TARGET,
        SUPPORTING_MAP_TARGET,
        "PostQMStatEntropySemanticsGapBoundedAttackSelectionStatus",
        "PostQMStatEntropySemanticsGapBoundedAttackSelectionDecision",
        "returnToFullPillarTargetMapNextLaneSelection",
        "post_qm_stat_entropy_semantics_gap_selection_consumes_live_target_v0",
        "post_qm_stat_entropy_semantics_gap_selection_consumes_review_token_v0",
        "post_qm_stat_entropy_semantics_gap_selection_review_consumed_v0",
        "post_qm_stat_entropy_semantics_gap_selection_supplied_only_preserved_v0",
        "post_qm_stat_entropy_semantics_gap_selection_exactly_one_target_v0",
        "post_qm_stat_entropy_semantics_gap_selection_output_token_v0",
        "post_qm_stat_entropy_semantics_gap_selection_decision_v0",
        "post_qm_stat_entropy_semantics_gap_selection_selected_target_v0",
        "post_qm_stat_entropy_semantics_gap_selection_candidate_count_v0",
    }:
        assert token in text

    assert (
        "import ToeFormal.Derivation.PostQMStatEntropySemanticsGapBoundedAttackSelection"
        in aggregate_text
    )


def test_post_qm_stat_entropy_semantics_gap_selection_surface_preserves_nonclaims() -> None:
    text = _read(SELECTION_PATH)

    for theorem in {
        "post_qm_stat_entropy_semantics_gap_selection_does_not_execute_target_v0",
        "post_qm_stat_entropy_semantics_gap_selection_no_lean_backed_discharge_v0",
        "post_qm_stat_entropy_semantics_gap_selection_no_gap_closure_v0",
        "post_qm_stat_entropy_semantics_gap_selection_no_qm_stat_completion_v0",
        "post_qm_stat_entropy_semantics_gap_selection_no_seam_closure_v0",
        "post_qm_stat_entropy_semantics_gap_selection_no_phase2_readiness_v0",
        "post_qm_stat_entropy_semantics_gap_selection_no_empirical_adequacy_v0",
        "post_qm_stat_entropy_semantics_gap_selection_no_canonical_toe_claim_v0",
        "post_qm_stat_entropy_semantics_gap_selection_master_action_not_promoted_v0",
        "post_qm_stat_entropy_semantics_gap_selection_qft_gr_not_authorized_v0",
        "post_qm_stat_entropy_semantics_gap_selection_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_post_qm_stat_entropy_semantics_gap_selection_report_selects_full_pillar_return() -> None:
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
    assert report["source_attack_surface"] == ATTACK_EVIDENCE
    assert report["source_attack_report"] == ATTACK_REPORT_EVIDENCE
    assert report["selection_surface"] == SELECTION_EVIDENCE
    assert report["focused_gate"] == (
        "formal/python/tests/test_post_qm_stat_entropy_semantics_gap_bounded_attack_selection_gate.py"
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
        SUPPORTING_MAP_TARGET,
    }


def test_post_qm_stat_entropy_semantics_gap_selection_report_preserves_review_boundary() -> None:
    report = _json(REPORT_PATH)

    assert report["review_interpretation"] == {
        "supplied_only_result_review_consumed": True,
        "selected_gap": SELECTED_GAP,
        "selected_obligation": SELECTED_OBLIGATION,
        "target_stat_entropy_semantics_authority": (
            "SUPPLIED_ONLY_TARGET_STAT_ENTROPY_SEMANTICS_RETAINED"
        ),
        "theorem_gap_discharged": False,
    }
    assert report["next_target_expectations"] == {
        "target_id": SELECTED_TARGET,
        "selector_should_choose_from_global_map": True,
        "selector_executes_selected_lane": False,
        "must_preserve_supplied_only_qm_stat_entropy_semantics_boundary": True,
    }
    assert report["nonclaim_boundaries"] == {
        "target_stat_entropy_semantics_lean_backed": False,
        "target_stat_entropy_semantics_supplied_only": True,
        "theorem_gap_discharged": False,
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


def test_post_qm_stat_entropy_semantics_gap_selection_registry_rotates_to_full_pillar() -> None:
    assert_current_target_consistent()
    payload = loop_registry()
    state = payload["current_target_state"]

    assert state["previous_live_next_target"] == SELECTION_TARGET
    assert state["live_next_target"] == SELECTED_TARGET
    assert state["live_next_target_evidence"] == SELECTION_EVIDENCE
    assert state["active_lane"] == ACTIVE_LANE

    previous_workstream = workstream(PREVIOUS_WORKSTREAM, payload)
    assert previous_workstream["status"] == "paused"
    assert previous_workstream["authorized_next_strict_target"] == SELECTION_TARGET
    assert previous_workstream["review_token"] == CONSUMED_REVIEW_TOKEN
    assert previous_workstream["selected_next_target"] == SELECTION_TARGET
    assert previous_workstream["target_stat_entropy_semantics_supplied_only"] == "yes"
    assert previous_workstream["theorem_gap_discharged"] == "no"

    current = active_workstream(payload)
    assert current["workstream_id"] == ACTIVE_LANE
    assert current["authorization_evidence"] == SELECTION_EVIDENCE
    assert current["authorized_next_strict_target"] == SELECTED_TARGET
    assert current["consumed_target"] == SELECTION_TARGET
    assert current["latest_surface"] == SURFACE_ID
    assert current["selection_report"] == REPORT_EVIDENCE
    assert current["consumed_review_token"] == CONSUMED_REVIEW_TOKEN
    assert current["output_token"] == OUTPUT_TOKEN
    assert current["selected_gap"] == SELECTED_GAP
    assert current["selected_next_target"] == SELECTED_TARGET
    assert current["selected_decision"] == SELECTED_TARGET
    assert current["selection_count"] == 1
    assert current["candidate_target_count"] == 2
    assert current["selection_executes_target"] == "no"
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
        "post_qm_stat_entropy_semantics_gap_bounded_attack_selection_nonclaim_boundary"
        in payload["retained_blocker_coverage"]
    )


def test_post_qm_stat_entropy_semantics_gap_selection_public_surfaces_are_synchronized() -> None:
    for path in {
        README_PATH,
        STATE_PATH,
        STRICT_MAP_PATH,
        CURRENT_AUTHORITATIVE_SURFACES_PATH,
    }:
        text = _read(path)
        for token in {
            f"CURRENT_LIVE_NEXT_TARGET_v0: {SELECTED_TARGET}",
            OUTPUT_TOKEN,
            "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_SUPPLIED_ONLY",
            "target STAT entropy semantics gap as supplied-only",
        }:
            assert token in text

    index_text = _read(CURRENT_AUTHORITATIVE_SURFACES_PATH)
    for token in {
        f"PREVIOUS_LIVE_NEXT_TARGET_v0: {SELECTION_TARGET}",
        f"CURRENT_LIVE_TARGET_EVIDENCE_v0: {SELECTION_EVIDENCE}",
        f"CURRENT_LIVE_TARGET_REPORT_v0: {REPORT_EVIDENCE}",
    }:
        assert token in index_text

    assert_public_surfaces_match_registry()
    assert_frontier_matches_registry()
    assert_forbidden_promotions_closed()


def test_post_qm_stat_entropy_semantics_gap_selection_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_post_qm_stat_entropy_semantics_gap_bounded_attack_selection_gate.py"
    )
