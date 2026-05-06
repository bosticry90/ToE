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
REVIEW_SURFACE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_SourceMapEligibilityLadderSummaryResultReview.lean"
)
SUMMARY_SURFACE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_SourceMapEligibilityLadderSummary.lean"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SOURCE_MAP_ELIGIBILITY_LADDER_SUMMARY_RESULT_REVIEW_20260503_v0.json"
)
SUMMARY_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SOURCE_MAP_ELIGIBILITY_LADDER_SUMMARY_20260503_v0.json"
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

SURFACE_ID = "qft_gr_source_map_eligibility_ladder_summary_result_review_v0"
SUMMARY_SURFACE_ID = "QFT_GR_SOURCE_MAP_ELIGIBILITY_LADDER_SUMMARY_v0"
PREVIOUS_TARGET = "review_qft_gr_source_map_eligibility_ladder_summary"
SELECTED_NEXT_TARGET = "select_next_post_qft_gr_ladder_bounded_attack"
POST_LADDER_SELECTED_TARGET = "return_to_full_pillar_target_map_next_lane_selection"
PROOF_DEBT_PREP_TARGET = "prepare_proof_debt_ledger_discharge_lane"
PROOF_DEBT_EXECUTION_TARGET = "execute_selected_proof_debt_discharge_item"
PROOF_DEBT_REVIEW_TARGET = "review_fnrep_nonalias_default_nonalias_discharge_result"
FINAL_TARGET = "select_next_post_proof_debt_discharge_bounded_attack"
CONSUMED_RESULT_TOKEN = "QFT_GR_SOURCE_MAP_ELIGIBILITY_LADDER_CONSTRUCTED_CLOSURE_NOT_AUTHORIZED"
REVIEW_RESULT_TOKEN = (
    "QFT_GR_SOURCE_MAP_ELIGIBILITY_LADDER_SUMMARY_RESULT_REVIEW_CONSUMED_CLOSURE_NOT_AUTHORIZED"
)
REPORT_ID = "QFT_GR_SOURCE_MAP_ELIGIBILITY_LADDER_SUMMARY_RESULT_REVIEW_20260503_v0"
RETAINED_BLOCKER = "PHASE1-BLOCKER-QFTGR-SOURCE-MAP-WITNESS-CHAIN-RETAINED"
REVIEW_LANE = "qft_gr_source_map_eligibility_ladder_summary_result_review"
SELECTION_LANE = "post_qft_gr_ladder_bounded_attack_selection"
FULL_PILLAR_LANE = "full_pillar_target_map_next_lane_selection"
ACTIVE_LANE = "proof_debt_ledger_discharge_lane"
FULL_PILLAR_SELECTION_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/FullPillarTargetMapNextLaneSelection.lean"
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
REVIEW_SURFACE_EVIDENCE = str(REVIEW_SURFACE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
SUMMARY_SURFACE_EVIDENCE = str(SUMMARY_SURFACE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
SUMMARY_REPORT_EVIDENCE = str(SUMMARY_REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _registry() -> dict[str, Any]:
    return _json(REGISTRY_PATH)


def test_source_map_eligibility_ladder_summary_result_review_surface_consumes_summary() -> None:
    text = _read(REVIEW_SURFACE_PATH)

    for token in {
        SURFACE_ID,
        PREVIOUS_TARGET,
        SELECTED_NEXT_TARGET,
        CONSUMED_RESULT_TOKEN,
        REVIEW_RESULT_TOKEN,
        "QFTGRSourceMapEligibilityLadderSummaryResultReviewStatus",
        "QFTGRSourceMapEligibilityLadderSummaryResultReviewDecision",
        "consumeSummaryAndSelectPostLadderBoundedAttack",
        "qft_gr_source_map_eligibility_ladder_summary_result_review_consumes_live_target_v0",
        "qft_gr_source_map_eligibility_ladder_summary_result_review_consumes_summary_v0",
        "qft_gr_source_map_eligibility_ladder_summary_result_review_map_only_v0",
        "qft_gr_source_map_eligibility_ladder_summary_result_review_witness_chain_absent_v0",
        "qft_gr_source_map_eligibility_ladder_summary_result_review_token_v0",
        "qft_gr_source_map_eligibility_ladder_summary_result_review_selected_next_target_v0",
        "qft_gr_source_map_eligibility_ladder_summary_result_review_selected_decision_v0",
        "qft_gr_source_map_eligibility_ladder_summary_result_review_layer_count_v0",
        "qft_gr_source_map_eligibility_ladder_summary_result_review_missing_witness_count_v0",
    }:
        assert token in text

    assert "qftGRSourceMapEligibilityLadderSummaryResultTokenId" in text
    assert "qftGRSourceMapEligibilitySuppliedOnlyLayerIdsV0" in text
    assert "qftGRSourceMapEligibilityMissingWitnessIdsV0" in text


def test_source_map_eligibility_ladder_summary_result_review_preserves_nonclaim_boundaries() -> None:
    text = _read(REVIEW_SURFACE_PATH)

    for theorem in {
        "qft_gr_source_map_eligibility_ladder_summary_result_review_witness_search_not_authorized_v0",
        "qft_gr_source_map_eligibility_ladder_summary_result_review_source_map_not_authorized_v0",
        "qft_gr_source_map_eligibility_ladder_summary_result_review_no_seam_closure_v0",
        "qft_gr_source_map_eligibility_ladder_summary_result_review_phase2_not_authorized_v0",
        "qft_gr_source_map_eligibility_ladder_summary_result_review_no_empirical_claim_v0",
        "qft_gr_source_map_eligibility_ladder_summary_result_review_master_action_not_promoted_v0",
        "qft_gr_source_map_eligibility_ladder_summary_result_review_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_source_map_eligibility_ladder_summary_result_review_report_records_selector_rotation() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["current_target"] == PREVIOUS_TARGET
    assert report["consumed_result_token"] == CONSUMED_RESULT_TOKEN
    assert report["review_result_token"] == REVIEW_RESULT_TOKEN
    assert report["review_surface"] == REVIEW_SURFACE_EVIDENCE
    assert report["summary_surface"] == SUMMARY_SURFACE_EVIDENCE
    assert report["summary_report"] == SUMMARY_REPORT_EVIDENCE
    assert report["selected_next_target"] == SELECTED_NEXT_TARGET
    assert report["selected_decision"] == (
        "consume_summary_and_select_post_ladder_bounded_attack"
    )
    assert report["recommended_selector_choice"] == (
        "return_to_full_pillar_target_map_next_lane_selection"
    )
    assert report["review_interpretation"] == (
        "source_map_eligibility_ladder_summary_consumed_as_dependency_obligation_map_only"
    )
    assert report["supplied_only_layers_count"] == 9
    assert report["missing_witnesses_count"] == 10
    assert report["review_effect"]["summary_consumed"] is True
    assert report["review_effect"]["dependency_obligation_map_only"] is True
    assert report["review_effect"]["witness_chain_absent"] is True
    assert report["review_effect"]["source_map_closure_authorized"] is False
    assert report["review_effect"]["witness_search_authorized"] is False
    assert report["retained_blocker"] == RETAINED_BLOCKER
    assert not any(report["nonclaim_boundaries"].values())
    assert report["next_action"] == SELECTED_NEXT_TARGET


def test_registry_rotates_to_post_qft_gr_ladder_selector() -> None:
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
    assert state["active_lane"] == ACTIVE_LANE
    assert REVIEW_LANE in state["paused_lanes"]
    assert SELECTION_LANE in state["paused_lanes"]
    assert FULL_PILLAR_LANE in state["paused_lanes"]

    review = workstream(REVIEW_LANE, payload)
    assert review["status"] == "paused"
    assert review["authorized_next_strict_target"] == SELECTED_NEXT_TARGET
    assert review["review_result_token"] == REVIEW_RESULT_TOKEN
    assert review["review_interpretation"] == (
        "source_map_eligibility_ladder_summary_consumed_as_dependency_obligation_map_only"
    )
    assert review["source_map_eligibility_ladder_constructed"] == (
        "yes_obligation_ladder_only"
    )
    assert review["witness_chain_status"] == "absent"
    assert review["witness_search_micro_lane_authorized"] == "no"
    assert review["full_source_map_closure_authorized"] == "no"

    selection = workstream(SELECTION_LANE, payload)
    assert selection["status"] == "paused"
    assert selection["authorized_next_strict_target"] == POST_LADDER_SELECTED_TARGET
    assert selection["consumed_target"] == SELECTED_NEXT_TARGET
    assert selection["source_review_surface"] == REVIEW_SURFACE_EVIDENCE
    assert selection["source_review_report"] == REPORT_EVIDENCE
    assert selection["consumed_review_token"] == REVIEW_RESULT_TOKEN
    assert selection["selection_scope"] == "post_qft_gr_ladder_bounded_attack_selection_only"
    assert selection["recommended_default_selection"] == (
        "return_to_full_pillar_target_map_next_lane_selection"
    )
    assert selection["qft_gr_witness_search_plan_selected"] == "no"
    assert selection["full_source_map_closure_authorized"] == "no"

    full_pillar = workstream(FULL_PILLAR_LANE, payload)
    assert full_pillar["status"] == "paused"
    assert full_pillar["authorized_next_strict_target"] == PROOF_DEBT_PREP_TARGET
    assert full_pillar["consumed_target"] == POST_LADDER_SELECTED_TARGET
    assert full_pillar["result_token"] == FULL_PILLAR_SELECTION_TOKEN

    active = workstream(ACTIVE_LANE, payload)
    assert active["status"] == "active"
    assert active["authorized_next_strict_target"] == FINAL_TARGET
    assert active["consumed_target"] == PROOF_DEBT_REVIEW_TARGET
    assert active["consumed_selection_token"] == FULL_PILLAR_SELECTION_TOKEN
    assert active["preparation_surface"] == PROOF_DEBT_PREPARATION_EVIDENCE
    assert active["preparation_result_token"] == PROOF_DEBT_PREPARATION_TOKEN
    assert active["execution_surface"] == PROOF_DEBT_DISCHARGE_EVIDENCE
    assert active["discharge_result_token"] == PROOF_DEBT_DISCHARGE_TOKEN
    assert active["result_token"] == PROOF_DEBT_RESULT_REVIEW_TOKEN

    qft_gr = workstream("qft_gr_source_map", payload)
    assert qft_gr["authorized_next_strict_target"] == FINAL_TARGET
    assert qft_gr["qft_gr_source_map_eligibility_ladder_summary_result_review_status"] == (
        "completed"
    )
    assert qft_gr["qft_gr_source_map_eligibility_ladder_summary_result_review_token"] == (
        REVIEW_RESULT_TOKEN
    )
    assert qft_gr["witness_chain_status"] == "absent"
    assert qft_gr["full_source_map_closure_authorized"] == "no"

    edges = {
        (edge["from"], edge["to"], edge["evidence"])
        for edge in payload["dependency_edges"]
        if edge["status"] == "active"
    }
    assert (
        REVIEW_LANE,
        SELECTION_LANE,
        REVIEW_SURFACE_EVIDENCE,
    ) in edges


def test_public_surfaces_record_source_map_eligibility_ladder_summary_review() -> None:
    for path in {
        README_PATH,
        STATE_PATH,
        ROADMAP_PATH,
        STRICT_MAP_PATH,
        SEAM_REGISTRY_PATH,
        SEAM_INVENTORY_PATH,
    }:
        text = _read(path)
        assert SELECTED_NEXT_TARGET in text
        assert REVIEW_SURFACE_EVIDENCE in text
        assert REPORT_EVIDENCE in text
        assert REVIEW_RESULT_TOKEN in text

    inventory = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-QFTGR-SOURCE-MAP-ELIGIBILITY-LADDER-SUMMARY-RESULT-REVIEW-v0" in inventory
    assert REVIEW_SURFACE_EVIDENCE in inventory
    assert REPORT_EVIDENCE in inventory


def test_source_map_eligibility_ladder_summary_result_review_gate_is_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_source_map_eligibility_ladder_summary_result_review_gate.py"
    )
