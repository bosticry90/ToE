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
    / "Derivation"
    / "FullPillarTargetMapNextLaneSelection.lean"
)
POST_QFT_SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "PostQFTGRLadderBoundedAttackSelection.lean"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_20260503_v0.json"
)
POST_QFT_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "POST_QFT_GR_LADDER_BOUNDED_ATTACK_SELECTION_20260503_v0.json"
)
TARGET_MAP_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "FullPillarTargetMapRebase.lean"
)
TARGET_MAP_DOC_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "FULL_PILLAR_TARGET_MAP_REBASE_v0.md"
)
PROOF_DEBT_LEDGER_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "LEAN_AXIOM_SPEC_BACKED_LEDGER_v0.md"
)
DISCHARGE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "FNRepNonAliasEquivalence01Discharge.lean"
)
RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "FNRepNonAliasEquivalence01DischargeResultReview.lean"
)
DISCHARGE_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PROOF_DEBT_DISCHARGE_FNREP_NONALIAS_20260503_v0.json"
)
RESULT_REVIEW_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PROOF_DEBT_DISCHARGE_FNREP_NONALIAS_RESULT_REVIEW_20260503_v0.json"
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

SURFACE_ID = "full_pillar_target_map_next_lane_selection_v0"
CONSUMED_TARGET = "return_to_full_pillar_target_map_next_lane_selection"
SELECTED_TARGET = "prepare_proof_debt_ledger_discharge_lane"
EXECUTION_TARGET = "execute_selected_proof_debt_discharge_item"
REVIEW_TARGET = "review_fnrep_nonalias_default_nonalias_discharge_result"
FINAL_TARGET = "select_next_post_proof_debt_discharge_bounded_attack"
CONSUMED_TOKEN = "POST_QFT_GR_LADDER_NEXT_ATTACK_SELECTED"
RESULT_TOKEN = "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTED"
PROOF_DEBT_PREPARED_TOKEN = "PROOF_DEBT_LEDGER_DISCHARGE_LANE_PREPARED"
DISCHARGE_RESULT_TOKEN = "FNREP_NONALIAS_DEFAULT_NONALIAS_DISCHARGED_LEAN_BACKED"
REVIEW_RESULT_TOKEN = (
    "FNREP_NONALIAS_DEFAULT_NONALIAS_DISCHARGE_RESULT_REVIEW_CONSUMED_LEAN_BACKED"
)
REPORT_ID = "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_20260503_v0"
SELECTION_LANE = "full_pillar_target_map_next_lane_selection"
ACTIVE_LANE = "proof_debt_ledger_discharge_lane"
SELECTED_LANE = "PROOF_DEBT_LEDGER_DISCHARGE_LANE"
SELECTED_SLICE = "proof_debt_ledger_discharge_lane_preparation_v0"
FINAL_SLICE = "proof_debt_ledger_discharge_item_execution_v0"
RESULT_REVIEW_SLICE = "fnrep_nonalias_default_nonalias_discharge_result_review_v0"
SELECTOR_SLICE = "post_proof_debt_discharge_bounded_attack_selection_v0"
PROOF_DEBT_PREPARATION_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/ProofDebtLedgerDischargeLane.lean"
)
PROOF_DEBT_PREPARATION_REPORT = (
    "formal/docs/release/PROOF_DEBT_LEDGER_DISCHARGE_LANE_20260503_v0.json"
)
DISCHARGE_EVIDENCE = str(DISCHARGE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
RESULT_REVIEW_EVIDENCE = str(RESULT_REVIEW_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
DISCHARGE_REPORT_EVIDENCE = str(DISCHARGE_REPORT_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
RESULT_REVIEW_REPORT_EVIDENCE = str(
    RESULT_REVIEW_REPORT_PATH.relative_to(REPO_ROOT)
).replace("\\", "/")
SELECTION_EVIDENCE = str(SELECTION_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
POST_QFT_SELECTION_EVIDENCE = str(
    POST_QFT_SELECTION_PATH.relative_to(REPO_ROOT)
).replace("\\", "/")
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
POST_QFT_REPORT_EVIDENCE = str(POST_QFT_REPORT_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
TARGET_MAP_EVIDENCE = str(TARGET_MAP_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
TARGET_MAP_DOC_EVIDENCE = str(TARGET_MAP_DOC_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
PROOF_DEBT_LEDGER_EVIDENCE = str(PROOF_DEBT_LEDGER_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
CANDIDATE_CLASSES = {
    "QFT_GR_WITNESS_SEARCH_PLAN",
    "GR_WEAK_FIELD_SOURCE_SIDE_OBLIGATION_LANE",
    "QM_STAT_THEOREM_GAP_RE_ENTRY_LANE",
    "SR_COSMO_GLOBAL_OBSTRUCTION_FOLLOW_UP",
    "MASTER_ACTION_DEPENDENCY_AUDIT",
    "PROOF_DEBT_LEDGER_DISCHARGE_LANE",
    "PILLAR_MAP_STALE_TARGET_SYNCHRONIZATION_LANE",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _registry() -> dict[str, Any]:
    return _json(REGISTRY_PATH)


def test_full_pillar_next_lane_selection_surface_selects_one_lane() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        CONSUMED_TOKEN,
        RESULT_TOKEN,
        SELECTED_LANE,
        SELECTED_TARGET,
        "FullPillarTargetMapNextLaneSelectionStatus",
        "FullPillarTargetMapNextLaneSelectionDecision",
        "selectProofDebtLedgerDischargeLane",
        "full_pillar_target_map_next_lane_selection_consumes_return_target_v0",
        "full_pillar_target_map_next_lane_selection_consumes_selector_token_v0",
        "full_pillar_target_map_next_lane_selection_rows_evaluated_v0",
        "full_pillar_target_map_next_lane_selection_ledger_attached_v0",
        "full_pillar_target_map_next_lane_selection_exactly_one_lane_v0",
        "full_pillar_target_map_next_lane_selection_result_token_v0",
        "full_pillar_target_map_next_lane_selection_selected_lane_v0",
        "full_pillar_target_map_next_lane_selection_selected_target_v0",
        "full_pillar_target_map_next_lane_selection_candidate_count_v0",
    } | CANDIDATE_CLASSES:
        assert token in text


def test_full_pillar_next_lane_selection_surface_preserves_nonclaim_boundaries() -> None:
    text = _read(SELECTION_PATH)

    for theorem in {
        "full_pillar_target_map_next_lane_selection_does_not_execute_lane_v0",
        "full_pillar_target_map_next_lane_selection_qft_gr_witness_not_selected_v0",
        "full_pillar_target_map_next_lane_selection_no_pillar_completion_v0",
        "full_pillar_target_map_next_lane_selection_no_seam_closure_v0",
        "full_pillar_target_map_next_lane_selection_no_phase2_readiness_v0",
        "full_pillar_target_map_next_lane_selection_no_empirical_adequacy_v0",
        "full_pillar_target_map_next_lane_selection_master_action_not_promoted_v0",
    }:
        assert theorem in text


def test_full_pillar_next_lane_selection_report_records_proof_debt_selection() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["selection_status"] == "completed_selection_only"
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_selector_token"] == CONSUMED_TOKEN
    assert report["result_token"] == RESULT_TOKEN
    assert report["post_qft_gr_selection_surface"] == POST_QFT_SELECTION_EVIDENCE
    assert report["post_qft_gr_selection_report"] == POST_QFT_REPORT_EVIDENCE
    assert report["target_map_surface"] == TARGET_MAP_EVIDENCE
    assert report["target_map_document"] == TARGET_MAP_DOC_EVIDENCE
    assert report["proof_debt_ledger"] == PROOF_DEBT_LEDGER_EVIDENCE
    assert report["selection_surface"] == SELECTION_EVIDENCE
    assert report["focused_gate"] == (
        "formal/python/tests/test_full_pillar_target_map_next_lane_selection_gate.py"
    )
    assert report["authorized_effect"] == "SELECT_EXACTLY_ONE_NEXT_BOUNDED_LANE"
    assert report["selection_executes_lane"] is False
    assert report["selection_count"] == 1
    assert report["candidate_lane_count"] == 7
    assert report["selected_lane"] == SELECTED_LANE
    assert report["selected_next_target"] == SELECTED_TARGET
    assert report["selected_next_target_kind"] == "proof_debt_lane_preparation_only"

    selected = [row for row in report["candidate_classes"] if row["selection"] == "selected"]
    assert len(selected) == 1
    assert selected[0]["class_id"] == SELECTED_LANE
    assert selected[0]["candidate_target"] == SELECTED_TARGET
    assert {row["class_id"] for row in report["candidate_classes"]} == CANDIDATE_CLASSES

    forbidden = report["nonclaim_boundaries"]
    assert forbidden == {
        "qft_gr_witness_search_selected": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "phase2_readiness_claim": False,
        "empirical_adequacy_claim": False,
        "master_action_promotion_authorized": False,
        "selection_executes_lane": False,
    }
    assert report["next_action_after_selection_packet"] == SELECTED_TARGET


def test_registry_rotates_to_proof_debt_ledger_discharge_preparation() -> None:
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_forbidden_promotions_closed()
    assert_public_surfaces_match_registry()
    payload = _registry()
    skip_if_not_current_target(payload, FINAL_TARGET)
    state = payload["current_target_state"]

    assert state["previous_live_next_target"] == REVIEW_TARGET
    assert state["live_next_target"] == FINAL_TARGET
    assert state["live_next_target_evidence"] == RESULT_REVIEW_EVIDENCE
    assert state["active_lane"] == ACTIVE_LANE
    assert SELECTION_LANE in state["paused_lanes"]

    selector = workstream(SELECTION_LANE, payload)
    assert selector["status"] == "paused"
    assert selector["retained_blocker"] == "full_pillar_target_map_next_lane_selection_nonclaim_boundary"
    assert selector["authorization_evidence"] == SELECTION_EVIDENCE
    assert selector["authorized_next_slice"] == SELECTED_SLICE
    assert selector["authorized_next_strict_target"] == SELECTED_TARGET
    assert selector["consumed_target"] == CONSUMED_TARGET
    assert selector["latest_surface"] == SURFACE_ID
    assert selector["selection_surface"] == SELECTION_EVIDENCE
    assert selector["selection_report"] == REPORT_EVIDENCE
    assert selector["result_token"] == RESULT_TOKEN
    assert selector["selected_lane"] == SELECTED_LANE
    assert selector["selected_next_target"] == SELECTED_TARGET
    assert selector["candidate_lane_count"] == 7
    assert selector["selection_count"] == 1
    assert selector["qft_gr_witness_search_selected"] == "no"
    assert selector["selection_executes_lane"] == "no"
    assert selector["pillar_completion_inferred"] == "no"
    assert selector["master_action_promotion_authorized"] == "no"

    active = workstream(ACTIVE_LANE, payload)
    assert active["status"] == "active"
    assert (
        active["retained_blocker"]
        == "fnrep_nonalias_default_nonalias_discharge_result_review_nonclaim_boundary"
    )
    assert active["authorization_evidence"] == RESULT_REVIEW_EVIDENCE
    assert active["authorized_next_slice"] == SELECTOR_SLICE
    assert active["authorized_next_strict_target"] == FINAL_TARGET
    assert active["consumed_target"] == REVIEW_TARGET
    assert active["latest_surface"] == "fnrep_nonalias_default_nonalias_discharge_result_review_v0"
    assert active["source_selection_surface"] == SELECTION_EVIDENCE
    assert active["source_selection_report"] == REPORT_EVIDENCE
    assert active["consumed_selection_token"] == RESULT_TOKEN
    assert active["preparation_surface"] == PROOF_DEBT_PREPARATION_EVIDENCE
    assert active["preparation_report"] == PROOF_DEBT_PREPARATION_REPORT
    assert active["execution_surface"] == DISCHARGE_EVIDENCE
    assert active["execution_report"] == DISCHARGE_REPORT_EVIDENCE
    assert active["review_surface"] == RESULT_REVIEW_EVIDENCE
    assert active["review_report"] == RESULT_REVIEW_REPORT_EVIDENCE
    assert active["preparation_result_token"] == PROOF_DEBT_PREPARED_TOKEN
    assert active["discharge_result_token"] == DISCHARGE_RESULT_TOKEN
    assert active["result_token"] == REVIEW_RESULT_TOKEN
    assert active["selected_lane"] == SELECTED_LANE
    assert active["proof_debt_ledger"] == PROOF_DEBT_LEDGER_EVIDENCE
    assert active["proof_debt_discharge_execution_authorized"] == (
        "completed_result_review_selector_selected"
    )
    assert active["selected_debt_item"] == (
        "formal/toe_formal/ToeFormal/Variational/FNRepNonAliasEquivalence01.lean::defaultNonAlias"
    )
    assert active["debt_item_discharged"] == "yes"
    assert active["pillar_completion_inferred"] == "no"
    assert active["seam_closure_claim"] == "no"
    assert active["phase2_readiness_claim"] == "no"
    assert active["empirical_adequacy_claim"] == "no"
    assert active["master_action_promotion_authorized"] == "no"

    qft_gr = workstream("qft_gr_source_map", payload)
    assert qft_gr["authorized_next_strict_target"] == FINAL_TARGET
    assert qft_gr["qft_gr_witness_search_plan_selected"] == "no"
    assert qft_gr["full_source_map_closure_authorized"] == "no"

    master_action = workstream("master_action_dependency_frontier", payload)
    assert master_action["authorized_next_strict_target"] == FINAL_TARGET
    assert master_action["master_action_current_citation_target"] == FINAL_TARGET
    assert master_action["master_action_promotion_authorized"] == "no"

    assert SELECTED_TARGET in payload["next_strict_target_coverage"]
    assert REVIEW_TARGET in payload["next_strict_target_coverage"]
    assert FINAL_TARGET in payload["next_strict_target_coverage"]
    assert "full_pillar_target_map_next_lane_selection_nonclaim_boundary" in payload[
        "retained_blocker_coverage"
    ]
    assert "proof_debt_ledger_discharge_lane_nonclaim_boundary" in payload[
        "retained_blocker_coverage"
    ]
    assert "proof_debt_ledger_discharge_lane_prepared_nonclaim_boundary" in payload[
        "retained_blocker_coverage"
    ]
    edges = {
        (edge["from"], edge["to"], edge["evidence"])
        for edge in payload["dependency_edges"]
        if edge["status"] == "active"
    }
    assert (SELECTION_LANE, ACTIVE_LANE, SELECTION_EVIDENCE) in edges


def test_public_surfaces_track_full_pillar_next_lane_selector() -> None:
    for path in [
        README_PATH,
        STATE_PATH,
        ROADMAP_PATH,
        STRICT_MAP_PATH,
        SEAM_REGISTRY_PATH,
        SEAM_INVENTORY_PATH,
    ]:
        text = _read(path)
        assert SELECTED_TARGET in text
        assert SELECTION_EVIDENCE in text
        assert REPORT_EVIDENCE in text
        assert RESULT_TOKEN in text

    inventory = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-FULL-PILLAR-TARGET-MAP-NEXT-LANE-SELECTION-v0" in inventory
    assert SELECTION_EVIDENCE in inventory
    assert REPORT_EVIDENCE in inventory
    assert SELECTED_TARGET in inventory
    assert RESULT_TOKEN in inventory

    assert_focused_gate_not_manifest_enrolled(
        "test_full_pillar_target_map_next_lane_selection_gate.py"
    )
