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
SURFACE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_SourceMapEligibilityLadderSummary.lean"
)
SOURCE_REVIEW_SURFACE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_PoissonRecoveryObligationSemanticsResultReview.lean"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SOURCE_MAP_ELIGIBILITY_LADDER_SUMMARY_20260503_v0.json"
)
SOURCE_REVIEW_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_POISSON_RECOVERY_OBLIGATION_SEMANTICS_RESULT_REVIEW_20260503_v0.json"
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

SURFACE_ID = "QFT_GR_SOURCE_MAP_ELIGIBILITY_LADDER_SUMMARY_v0"
SOURCE_REVIEW_SURFACE_ID = "qft_gr_poisson_recovery_obligation_semantics_result_review_v0"
PREVIOUS_TARGET = "prepare_qft_gr_source_map_eligibility_ladder_summary"
SELECTED_NEXT_TARGET = "review_qft_gr_source_map_eligibility_ladder_summary"
CONSUMED_REVIEW_TOKEN = (
    "QFT_GR_POISSON_RECOVERY_OBLIGATION_SEMANTICS_RESULT_REVIEW_CONSUMED_SUPPLIED_ONLY"
)
RESULT_TOKEN = "QFT_GR_SOURCE_MAP_ELIGIBILITY_LADDER_CONSTRUCTED_CLOSURE_NOT_AUTHORIZED"
REPORT_ID = "QFT_GR_SOURCE_MAP_ELIGIBILITY_LADDER_SUMMARY_20260503_v0"
RETAINED_BLOCKER = "PHASE1-BLOCKER-QFTGR-SOURCE-MAP-WITNESS-CHAIN-RETAINED"
SOURCE_RETAINED_BLOCKER = (
    "PHASE1-BLOCKER-QFTGR-SOURCE-MAP-ELIGIBILITY-LADDER-SUMMARY-RETAINED"
)
PREP_LANE = "qft_gr_source_map_eligibility_ladder_summary_preparation"
ACTIVE_LANE = "qft_gr_source_map_eligibility_ladder_summary_result_review"
POST_LADDER_SELECTION_TARGET = "select_next_post_qft_gr_ladder_bounded_attack"
POST_LADDER_SELECTED_TARGET = "return_to_full_pillar_target_map_next_lane_selection"
PROOF_DEBT_PREP_TARGET = "prepare_proof_debt_ledger_discharge_lane"
PROOF_DEBT_EXECUTION_TARGET = "execute_selected_proof_debt_discharge_item"
PROOF_DEBT_REVIEW_TARGET = "review_fnrep_nonalias_default_nonalias_discharge_result"
FINAL_TARGET = "select_next_post_proof_debt_discharge_bounded_attack"
FULL_PILLAR_LANE = "full_pillar_target_map_next_lane_selection"
ACTIVE_LANE_AFTER_FULL_PILLAR_SELECTION = "proof_debt_ledger_discharge_lane"
SURFACE_EVIDENCE = str(SURFACE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
SOURCE_REVIEW_SURFACE_EVIDENCE = str(
    SOURCE_REVIEW_SURFACE_PATH.relative_to(REPO_ROOT)
).replace("\\", "/")
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
SOURCE_REVIEW_REPORT_EVIDENCE = str(
    SOURCE_REVIEW_REPORT_PATH.relative_to(REPO_ROOT)
).replace("\\", "/")


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _registry() -> dict[str, Any]:
    return _json(REGISTRY_PATH)


def test_source_map_eligibility_ladder_summary_surface_constructs_ladder() -> None:
    text = _read(SURFACE_PATH)

    for token in {
        SURFACE_ID,
        PREVIOUS_TARGET,
        SELECTED_NEXT_TARGET,
        CONSUMED_REVIEW_TOKEN,
        RESULT_TOKEN,
        "QFTGRSourceMapEligibilityLadderSummaryStatus",
        "QFTGRSourceMapEligibilityLadderSummaryDecision",
        "constructLadderAndReviewClosureNotAuthorized",
        "qft_gr_source_map_eligibility_ladder_summary_consumes_live_target_v0",
        "qft_gr_source_map_eligibility_ladder_summary_constructed_v0",
        "qft_gr_source_map_eligibility_ladder_summary_supplied_only_ladder_constructed_v0",
        "qft_gr_source_map_eligibility_ladder_summary_missing_witness_chain_listed_v0",
        "qft_gr_source_map_eligibility_ladder_summary_obligation_not_closure_v0",
        "qft_gr_source_map_eligibility_ladder_summary_consumes_poisson_review_v0",
        "qft_gr_source_map_eligibility_ladder_summary_result_token_v0",
        "qft_gr_source_map_eligibility_ladder_summary_selected_next_target_v0",
        "qft_gr_source_map_eligibility_ladder_summary_selected_decision_v0",
        "qft_gr_source_map_eligibility_ladder_summary_layer_count_v0",
        "qft_gr_source_map_eligibility_ladder_summary_missing_witness_count_v0",
        "qft_gr_source_map_eligibility_ladder_summary_pause_recommended_v0",
    }:
        assert token in text

    assert text.count("_semantics\"") >= 5
    assert "qft_gr_source_map_closure_witness" in text


def test_source_map_eligibility_ladder_summary_preserves_boundaries() -> None:
    text = _read(SURFACE_PATH)

    for theorem in {
        "qft_gr_source_map_eligibility_ladder_summary_witness_search_not_authorized_v0",
        "qft_gr_source_map_eligibility_ladder_summary_scheme_not_authorized_v0",
        "qft_gr_source_map_eligibility_ladder_summary_finiteness_not_authorized_v0",
        "qft_gr_source_map_eligibility_ladder_summary_hadamard_not_authorized_v0",
        "qft_gr_source_map_eligibility_ladder_summary_self_adjoint_not_authorized_v0",
        "qft_gr_source_map_eligibility_ladder_summary_domain_density_not_authorized_v0",
        "qft_gr_source_map_eligibility_ladder_summary_conservation_witness_not_authorized_v0",
        "qft_gr_source_map_eligibility_ladder_summary_actual_conservation_not_authorized_v0",
        "qft_gr_source_map_eligibility_ladder_summary_bianchi_witness_not_authorized_v0",
        "qft_gr_source_map_eligibility_ladder_summary_actual_bianchi_not_authorized_v0",
        "qft_gr_source_map_eligibility_ladder_summary_einstein_witness_not_authorized_v0",
        "qft_gr_source_map_eligibility_ladder_summary_actual_coupling_not_authorized_v0",
        "qft_gr_source_map_eligibility_ladder_summary_source_witness_not_authorized_v0",
        "qft_gr_source_map_eligibility_ladder_summary_actual_source_identification_not_authorized_v0",
        "qft_gr_source_map_eligibility_ladder_summary_poisson_witness_not_authorized_v0",
        "qft_gr_source_map_eligibility_ladder_summary_actual_poisson_not_authorized_v0",
        "qft_gr_source_map_eligibility_ladder_summary_newtonian_not_authorized_v0",
        "qft_gr_source_map_eligibility_ladder_summary_weak_field_proof_not_authorized_v0",
        "qft_gr_source_map_eligibility_ladder_summary_semiclassical_eq_not_authorized_v0",
        "qft_gr_source_map_eligibility_ladder_summary_source_map_not_authorized_v0",
        "qft_gr_source_map_eligibility_ladder_summary_no_seam_closure_v0",
        "qft_gr_source_map_eligibility_ladder_summary_no_semiclassical_claim_v0",
        "qft_gr_source_map_eligibility_ladder_summary_no_einstein_claim_v0",
        "qft_gr_source_map_eligibility_ladder_summary_phase2_not_authorized_v0",
        "qft_gr_source_map_eligibility_ladder_summary_master_action_not_promoted_v0",
        "qft_gr_source_map_eligibility_ladder_summary_no_empirical_claim_v0",
        "qft_gr_source_map_eligibility_ladder_summary_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_source_map_eligibility_ladder_summary_report_records_ladder() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["current_target"] == PREVIOUS_TARGET
    assert report["consumed_review_token"] == CONSUMED_REVIEW_TOKEN
    assert report["result_token"] == RESULT_TOKEN
    assert report["summary_surface"] == SURFACE_EVIDENCE
    assert report["source_review_surface"] == SOURCE_REVIEW_SURFACE_EVIDENCE
    assert report["source_review_report"] == SOURCE_REVIEW_REPORT_EVIDENCE
    assert report["selected_next_target"] == SELECTED_NEXT_TARGET
    assert report["recommended_post_review_selector"] == (
        "select_next_post_qft_gr_ladder_bounded_attack"
    )
    assert report["result_interpretation"] == (
        "obligation_ladder_constructed_witness_chain_absent_source_map_closure_not_authorized"
    )
    assert len(report["supplied_only_layers"]) == 9
    assert len(report["missing_witnesses"]) == 10
    assert report["summary_effect"]["ladder_constructed"] is True
    assert report["summary_effect"]["witness_chain_absent"] is True
    assert report["summary_effect"]["closure_authorized"] is False
    assert report["summary_effect"]["witness_search_authorized"] is False
    assert report["summary_effect"]["obligation_construction_is_closure_proof"] is False
    assert report["retained_blocker"] == RETAINED_BLOCKER
    assert not any(report["nonclaim_boundaries"].values())


def test_registry_rotates_to_source_map_eligibility_ladder_summary_review() -> None:
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_forbidden_promotions_closed()
    assert_public_surfaces_match_registry()
    payload = _registry()
    skip_if_not_current_target(payload, FINAL_TARGET)
    state = payload["current_target_state"]

    assert state["previous_live_next_target"] == PROOF_DEBT_REVIEW_TARGET
    assert state["live_next_target"] == FINAL_TARGET
    assert state["active_lane"] == ACTIVE_LANE_AFTER_FULL_PILLAR_SELECTION
    assert PREP_LANE in state["paused_lanes"]
    assert ACTIVE_LANE in state["paused_lanes"]
    assert FULL_PILLAR_LANE in state["paused_lanes"]

    prep = workstream(PREP_LANE, payload)
    assert prep["status"] == "paused"
    assert prep["authorized_next_strict_target"] == SELECTED_NEXT_TARGET
    assert prep["consumed_target"] == PREVIOUS_TARGET
    assert prep["latest_surface"] == SURFACE_ID
    assert prep["summary_surface"] == SURFACE_EVIDENCE
    assert prep["summary_report"] == REPORT_EVIDENCE
    assert prep["source_review_surface"] == SOURCE_REVIEW_SURFACE_EVIDENCE
    assert prep["source_review_report"] == SOURCE_REVIEW_REPORT_EVIDENCE
    assert prep["consumed_review_token"] == CONSUMED_REVIEW_TOKEN
    assert prep["result_token"] == RESULT_TOKEN
    assert prep["summary_result"] == (
        "obligation_ladder_constructed_witness_chain_absent_source_map_closure_not_authorized"
    )
    assert prep["source_map_eligibility_ladder_constructed"] == (
        "yes_obligation_ladder_only"
    )
    assert prep["supplied_only_layers_count"] == 9
    assert prep["missing_witnesses_count"] == 10
    assert prep["witness_chain_status"] == "absent"
    assert prep["witness_search_micro_lane_authorized"] == "no"
    assert prep["full_source_map_closure_authorized"] == "no"

    active = workstream(ACTIVE_LANE, payload)
    assert active["status"] == "paused"
    assert active["authorized_next_strict_target"] == POST_LADDER_SELECTION_TARGET
    assert active["consumed_target"] == SELECTED_NEXT_TARGET
    assert (
        active["latest_surface"]
        == "qft_gr_source_map_eligibility_ladder_summary_result_review_v0"
    )
    assert active["summary_result_token"] == RESULT_TOKEN
    assert active["review_scope"] == "summary_result_review_only"
    assert active["source_map_eligibility_ladder_constructed"] == (
        "yes_obligation_ladder_only"
    )
    assert active["witness_chain_status"] == "absent"
    assert active["witness_search_micro_lane_authorized"] == "no"
    assert active["full_source_map_closure_authorized"] == "no"
    assert active["qft_gr_seam_closed"] == "no"
    assert active["phase2_authorized"] == "no"
    assert active["master_action_promotion_authorized"] == "no"

    qft_gr = workstream("qft_gr_source_map", payload)
    assert qft_gr["retained_blocker"] == RETAINED_BLOCKER
    assert qft_gr["source_map_eligibility_ladder_summary_status"] == "completed"
    assert qft_gr["source_map_eligibility_ladder_summary_evidence"] == (
        SURFACE_EVIDENCE
    )
    assert qft_gr["source_map_eligibility_ladder_summary_result_token"] == (
        RESULT_TOKEN
    )
    assert qft_gr["source_map_eligibility_ladder_constructed"] == (
        "yes_obligation_ladder_only"
    )
    assert qft_gr["witness_chain_status"] == "absent"
    assert qft_gr["source_map_eligibility_ladder_summary_result_review_target"] == (
        SELECTED_NEXT_TARGET
    )
    assert qft_gr["authorized_next_strict_target"] == FINAL_TARGET
    assert qft_gr["full_source_map_closure_authorized"] == "no"
    assert qft_gr["witness_search_micro_lane_authorized"] == "no"

    assert SELECTED_NEXT_TARGET in payload["next_strict_target_coverage"]
    assert POST_LADDER_SELECTION_TARGET in payload["next_strict_target_coverage"]
    assert POST_LADDER_SELECTED_TARGET in payload["next_strict_target_coverage"]
    assert PROOF_DEBT_EXECUTION_TARGET in payload["next_strict_target_coverage"]
    assert PROOF_DEBT_REVIEW_TARGET in payload["next_strict_target_coverage"]
    assert FINAL_TARGET in payload["next_strict_target_coverage"]
    assert PREVIOUS_TARGET in payload["next_strict_target_coverage"]
    assert RETAINED_BLOCKER in payload["retained_blocker_coverage"]
    assert SOURCE_RETAINED_BLOCKER in payload["retained_blocker_coverage"]
    edges = {(edge["from"], edge["to"]) for edge in payload["dependency_edges"]}
    assert (PREP_LANE, ACTIVE_LANE) in edges


def test_public_surfaces_track_source_map_eligibility_ladder_summary() -> None:
    for path in [README_PATH, STATE_PATH, ROADMAP_PATH, STRICT_MAP_PATH]:
        text = _read(path)
        assert PREVIOUS_TARGET in text
        assert SELECTED_NEXT_TARGET in text
        assert "QFT_GR_SourceMapEligibilityLadderSummary.lean" in text
        assert RESULT_TOKEN in text

    for path in [SEAM_REGISTRY_PATH, SEAM_INVENTORY_PATH]:
        text = _read(path)
        assert SELECTED_NEXT_TARGET in text
        assert SURFACE_ID in text
        assert REPORT_EVIDENCE in text

    inventory_text = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-QFTGR-SOURCE-MAP-ELIGIBILITY-LADDER-SUMMARY-v0" in inventory_text
    assert SURFACE_EVIDENCE in inventory_text
    assert REPORT_EVIDENCE in inventory_text
    assert SELECTED_NEXT_TARGET in inventory_text

    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_source_map_eligibility_ladder_summary_gate.py"
    )
