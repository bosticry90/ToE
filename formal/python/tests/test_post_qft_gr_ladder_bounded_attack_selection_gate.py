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
    skip_if_not_current_target,
    workstream,
)


REPO_ROOT = find_repo_root(Path(__file__))
SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "PostQFTGRLadderBoundedAttackSelection.lean"
)
REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_SourceMapEligibilityLadderSummaryResultReview.lean"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "POST_QFT_GR_LADDER_BOUNDED_ATTACK_SELECTION_20260503_v0.json"
)
REVIEW_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SOURCE_MAP_ELIGIBILITY_LADDER_SUMMARY_RESULT_REVIEW_20260503_v0.json"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STRICT_MAP_PATH = (
    REPO_ROOT / "formal" / "docs" / "lanes" / "STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md"
)
SEAM_REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md"
)
SEAM_INVENTORY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md"
)
MATH_PHYSICS_INVENTORY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
)

SURFACE_ID = "post_qft_gr_ladder_bounded_attack_selection_v0"
SELECTION_TARGET = "select_next_post_qft_gr_ladder_bounded_attack"
SELECTED_TARGET = "return_to_full_pillar_target_map_next_lane_selection"
ALTERNATIVE_TARGET = "prepare_qft_gr_witness_search_plan"
CONSUMED_REVIEW_TARGET = "review_qft_gr_source_map_eligibility_ladder_summary"
CONSUMED_REVIEW_TOKEN = (
    "QFT_GR_SOURCE_MAP_ELIGIBILITY_LADDER_SUMMARY_RESULT_REVIEW_CONSUMED_CLOSURE_NOT_AUTHORIZED"
)
OUTPUT_TOKEN = "POST_QFT_GR_LADDER_NEXT_ATTACK_SELECTED"
REPORT_ID = "POST_QFT_GR_LADDER_BOUNDED_ATTACK_SELECTION_20260503_v0"
SELECTION_LANE = "post_qft_gr_ladder_bounded_attack_selection"
ACTIVE_LANE = "full_pillar_target_map_next_lane_selection"
PROOF_DEBT_PREP_TARGET = "prepare_proof_debt_ledger_discharge_lane"
PROOF_DEBT_EXECUTION_TARGET = "execute_selected_proof_debt_discharge_item"
PROOF_DEBT_REVIEW_TARGET = "review_fnrep_nonalias_default_nonalias_discharge_result"
FINAL_TARGET = "select_next_post_proof_debt_discharge_bounded_attack"
FINAL_ACTIVE_LANE = "proof_debt_ledger_discharge_lane"
FULL_PILLAR_SELECTION_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/FullPillarTargetMapNextLaneSelection.lean"
)
FULL_PILLAR_SELECTION_REPORT = (
    "formal/docs/release/FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_20260503_v0.json"
)
FULL_PILLAR_SELECTION_TOKEN = "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTED"
PROOF_DEBT_PREPARATION_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/ProofDebtLedgerDischargeLane.lean"
)
PROOF_DEBT_PREPARATION_TOKEN = "PROOF_DEBT_LEDGER_DISCHARGE_LANE_PREPARED"
PROOF_DEBT_DISCHARGE_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Variational/FNRepNonAliasEquivalence01Discharge.lean"
)
PROOF_DEBT_DISCHARGE_TOKEN = "FNREP_NONALIAS_DEFAULT_NONALIAS_DISCHARGED_LEAN_BACKED"
PROOF_DEBT_RESULT_REVIEW_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Variational/FNRepNonAliasEquivalence01DischargeResultReview.lean"
)
PROOF_DEBT_RESULT_REVIEW_TOKEN = (
    "FNREP_NONALIAS_DEFAULT_NONALIAS_DISCHARGE_RESULT_REVIEW_CONSUMED_LEAN_BACKED"
)
SELECTION_EVIDENCE = str(SELECTION_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REVIEW_EVIDENCE = str(REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REVIEW_REPORT_EVIDENCE = str(REVIEW_REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _registry() -> dict[str, Any]:
    return _json(REGISTRY_PATH)


def test_post_qft_gr_ladder_selection_surface_records_exactly_one_target() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        SURFACE_ID,
        SELECTION_TARGET,
        SELECTED_TARGET,
        ALTERNATIVE_TARGET,
        CONSUMED_REVIEW_TOKEN,
        OUTPUT_TOKEN,
        "PostQFTGRLadderBoundedAttackSelectionStatus",
        "PostQFTGRLadderBoundedAttackSelectionDecision",
        "returnToFullPillarTargetMapNextLaneSelection",
        "post_qft_gr_ladder_bounded_attack_selection_consumes_live_target_v0",
        "post_qft_gr_ladder_bounded_attack_selection_consumes_review_token_v0",
        "post_qft_gr_ladder_bounded_attack_selection_ladder_map_only_v0",
        "post_qft_gr_ladder_bounded_attack_selection_witness_chain_absent_v0",
        "post_qft_gr_ladder_bounded_attack_selection_exactly_one_target_v0",
        "post_qft_gr_ladder_bounded_attack_selection_output_token_v0",
        "post_qft_gr_ladder_bounded_attack_selection_decision_v0",
        "post_qft_gr_ladder_bounded_attack_selection_selected_target_v0",
        "post_qft_gr_ladder_bounded_attack_selection_candidate_count_v0",
    }:
        assert token in text


def test_post_qft_gr_ladder_selection_surface_preserves_nonclaim_boundaries() -> None:
    text = _read(SELECTION_PATH)

    for theorem in {
        "post_qft_gr_ladder_bounded_attack_selection_does_not_execute_target_v0",
        "post_qft_gr_ladder_bounded_attack_selection_witness_search_plan_not_selected_v0",
        "post_qft_gr_ladder_bounded_attack_selection_no_source_map_closure_v0",
        "post_qft_gr_ladder_bounded_attack_selection_no_seam_closure_v0",
        "post_qft_gr_ladder_bounded_attack_selection_no_phase2_readiness_v0",
        "post_qft_gr_ladder_bounded_attack_selection_no_empirical_adequacy_v0",
        "post_qft_gr_ladder_bounded_attack_selection_master_action_not_promoted_v0",
    }:
        assert theorem in text


def test_post_qft_gr_ladder_selection_report_records_cross_pillar_return() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["current_target"] == SELECTION_TARGET
    assert report["consumed_review_target"] == CONSUMED_REVIEW_TARGET
    assert report["consumed_review_token"] == CONSUMED_REVIEW_TOKEN
    assert report["output_token"] == OUTPUT_TOKEN
    assert report["selection_surface"] == SELECTION_EVIDENCE
    assert report["review_surface"] == REVIEW_EVIDENCE
    assert report["review_report"] == REVIEW_REPORT_EVIDENCE
    assert report["authorized_effect"] == "SELECT_EXACTLY_ONE_NEXT_BOUNDED_TARGET"
    assert report["selection_executes_target"] is False
    assert report["selection_count"] == 1
    assert report["selected_next_target"] == SELECTED_TARGET
    assert report["selected_decision"] == SELECTED_TARGET
    assert report["witness_chain_status"] == "absent"

    selected = [row for row in report["candidate_next_targets"] if row["selection"] == "selected"]
    assert len(selected) == 1
    assert selected[0]["target_id"] == SELECTED_TARGET
    assert {row["target_id"] for row in report["candidate_next_targets"]} == {
        SELECTED_TARGET,
        ALTERNATIVE_TARGET,
    }

    forbidden = report["nonclaim_boundaries"]
    assert forbidden == {
        "qft_gr_witness_search_plan_selected": False,
        "source_map_closure_inferred": False,
        "seam_closure_claim": False,
        "phase2_readiness_claim": False,
        "empirical_adequacy_claim": False,
        "master_action_promotion_authorized": False,
        "selection_executes_target": False,
    }


def test_registry_rotates_to_full_pillar_target_map_next_lane_selection() -> None:
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_forbidden_promotions_closed()
    assert_public_surfaces_match_registry()
    payload = _registry()
    skip_if_not_current_target(payload, FINAL_TARGET)
    state = payload["current_target_state"]

    assert state["previous_live_next_target"] == PROOF_DEBT_REVIEW_TARGET
    assert state["live_next_target"] == FINAL_TARGET
    assert state["live_next_target_evidence"] == PROOF_DEBT_RESULT_REVIEW_EVIDENCE
    assert state["active_lane"] == FINAL_ACTIVE_LANE
    assert SELECTION_LANE in state["paused_lanes"]
    assert ACTIVE_LANE in state["paused_lanes"]

    selector = workstream(SELECTION_LANE, payload)
    assert selector["status"] == "paused"
    assert selector["authorized_next_strict_target"] == SELECTED_TARGET
    assert selector["consumed_target"] == SELECTION_TARGET
    assert selector["latest_surface"] == SURFACE_ID
    assert selector["selection_surface"] == SELECTION_EVIDENCE
    assert selector["selection_report"] == REPORT_EVIDENCE
    assert selector["output_token"] == OUTPUT_TOKEN
    assert selector["selection_count"] == 1
    assert selector["candidate_target_count"] == 2
    assert selector["selected_next_target"] == SELECTED_TARGET
    assert selector["qft_gr_witness_search_plan_selected"] == "no"
    assert selector["selection_executes_target"] == "no"
    assert selector["full_source_map_closure_authorized"] == "no"

    full_pillar = workstream(ACTIVE_LANE, payload)
    assert full_pillar["status"] == "paused"
    assert full_pillar["authorized_next_strict_target"] == PROOF_DEBT_PREP_TARGET
    assert full_pillar["consumed_target"] == SELECTED_TARGET
    assert full_pillar["selection_surface"] == FULL_PILLAR_SELECTION_EVIDENCE
    assert full_pillar["selection_report"] == FULL_PILLAR_SELECTION_REPORT
    assert full_pillar["result_token"] == FULL_PILLAR_SELECTION_TOKEN
    assert full_pillar["selected_next_target"] == PROOF_DEBT_PREP_TARGET

    active = workstream(FINAL_ACTIVE_LANE, payload)
    assert active["status"] == "active"
    assert active["authorized_next_strict_target"] == FINAL_TARGET
    assert active["consumed_target"] == PROOF_DEBT_REVIEW_TARGET
    assert active["source_selection_surface"] == FULL_PILLAR_SELECTION_EVIDENCE
    assert active["source_selection_report"] == FULL_PILLAR_SELECTION_REPORT
    assert active["consumed_selection_token"] == FULL_PILLAR_SELECTION_TOKEN
    assert active["preparation_surface"] == PROOF_DEBT_PREPARATION_EVIDENCE
    assert active["preparation_result_token"] == PROOF_DEBT_PREPARATION_TOKEN
    assert active["execution_surface"] == PROOF_DEBT_DISCHARGE_EVIDENCE
    assert active["discharge_result_token"] == PROOF_DEBT_DISCHARGE_TOKEN
    assert active["result_token"] == PROOF_DEBT_RESULT_REVIEW_TOKEN
    assert active["qft_gr_witness_search_plan_selected"] == "no"
    assert active["full_source_map_closure_authorized"] == "no"
    assert active["seam_closure_claim"] == "no"
    assert active["phase2_readiness_claim"] == "no"
    assert active["empirical_adequacy_claim"] == "no"
    assert active["master_action_promotion_authorized"] == "no"

    assert SELECTED_TARGET in payload["next_strict_target_coverage"]
    assert PROOF_DEBT_PREP_TARGET in payload["next_strict_target_coverage"]
    assert FINAL_TARGET in payload["next_strict_target_coverage"]
    assert "post_qft_gr_ladder_bounded_attack_selection_nonclaim_boundary" in payload[
        "retained_blocker_coverage"
    ]
    edges = {
        (edge["from"], edge["to"], edge["evidence"])
        for edge in payload["dependency_edges"]
        if edge["status"] == "active"
    }
    assert (SELECTION_LANE, ACTIVE_LANE, SELECTION_EVIDENCE) in edges
    assert (ACTIVE_LANE, FINAL_ACTIVE_LANE, FULL_PILLAR_SELECTION_EVIDENCE) in edges


def test_public_surfaces_track_post_qft_gr_ladder_selector() -> None:
    for path in [README_PATH, STATE_PATH, ROADMAP_PATH, STRICT_MAP_PATH]:
        text = _read(path)
        assert SELECTED_TARGET in text
        assert SELECTION_EVIDENCE in text
        assert REPORT_EVIDENCE in text
        assert OUTPUT_TOKEN in text

    for path in [SEAM_REGISTRY_PATH, SEAM_INVENTORY_PATH]:
        text = _read(path)
        assert SELECTED_TARGET in text
        assert SELECTION_EVIDENCE in text
        assert REPORT_EVIDENCE in text
        assert OUTPUT_TOKEN in text

    inventory = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-POST-QFTGR-LADDER-BOUNDED-ATTACK-SELECTION-v0" in inventory
    assert SELECTION_EVIDENCE in inventory
    assert REPORT_EVIDENCE in inventory
    assert SELECTED_TARGET in inventory
    assert OUTPUT_TOKEN in inventory

    assert_focused_gate_not_manifest_enrolled(
        "test_post_qft_gr_ladder_bounded_attack_selection_gate.py"
    )
