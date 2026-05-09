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
    / "Derivation"
    / "ProofDebtLedgerDischargeLane.lean"
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
FULL_PILLAR_SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "FullPillarTargetMapNextLaneSelection.lean"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PROOF_DEBT_LEDGER_DISCHARGE_LANE_20260503_v0.json"
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
FULL_PILLAR_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_20260503_v0.json"
)
LEDGER_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "LEAN_AXIOM_SPEC_BACKED_LEDGER_v0.md"
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

SURFACE_ID = "proof_debt_ledger_discharge_lane_v0"
DISCHARGE_SURFACE_ID = "fnrep_nonalias_default_nonalias_discharge_v0"
RESULT_REVIEW_SURFACE_ID = "fnrep_nonalias_default_nonalias_discharge_result_review_v0"
CONSUMED_TARGET = "prepare_proof_debt_ledger_discharge_lane"
NEXT_TARGET = "execute_selected_proof_debt_discharge_item"
REVIEW_TARGET = "review_fnrep_nonalias_default_nonalias_discharge_result"
FINAL_TARGET = "select_next_post_proof_debt_discharge_bounded_attack"
CONSUMED_TOKEN = "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTED"
RESULT_TOKEN = "PROOF_DEBT_LEDGER_DISCHARGE_LANE_PREPARED"
DISCHARGE_RESULT_TOKEN = "FNREP_NONALIAS_DEFAULT_NONALIAS_DISCHARGED_LEAN_BACKED"
REVIEW_RESULT_TOKEN = (
    "FNREP_NONALIAS_DEFAULT_NONALIAS_DISCHARGE_RESULT_REVIEW_CONSUMED_LEAN_BACKED"
)
SELECTED_LANE = "PROOF_DEBT_LEDGER_DISCHARGE_LANE"
SELECTED_ITEM = (
    "formal/toe_formal/ToeFormal/Variational/FNRepNonAliasEquivalence01.lean::defaultNonAlias"
)
SELECTED_DECLARATION = "defaultNonAlias"
SELECTED_FILE = "formal/toe_formal/ToeFormal/Variational/FNRepNonAliasEquivalence01.lean"
CURRENT_AUTHORITY = "SPEC_BACKED_DECLARATION_LEVEL_WITNESS"
INTENDED_AUTHORITY = "LEAN_BACKED_THEOREM_OR_EXPLICIT_REFINEMENT"
ACTIVE_LANE = "proof_debt_ledger_discharge_lane"
SELECTED_SLICE = "proof_debt_ledger_discharge_item_execution_v0"
FINAL_SLICE = "fnrep_nonalias_default_nonalias_discharge_result_review_v0"
SELECTOR_SLICE = "post_proof_debt_discharge_bounded_attack_selection_v0"
SURFACE_EVIDENCE = str(SURFACE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
DISCHARGE_EVIDENCE = str(DISCHARGE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
RESULT_REVIEW_EVIDENCE = str(RESULT_REVIEW_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
FULL_PILLAR_SELECTION_EVIDENCE = str(
    FULL_PILLAR_SELECTION_PATH.relative_to(REPO_ROOT)
).replace("\\", "/")
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
DISCHARGE_REPORT_EVIDENCE = str(DISCHARGE_REPORT_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
RESULT_REVIEW_REPORT_EVIDENCE = str(
    RESULT_REVIEW_REPORT_PATH.relative_to(REPO_ROOT)
).replace("\\", "/")
FULL_PILLAR_REPORT_EVIDENCE = str(
    FULL_PILLAR_REPORT_PATH.relative_to(REPO_ROOT)
).replace("\\", "/")
LEDGER_EVIDENCE = str(LEDGER_PATH.relative_to(REPO_ROOT)).replace("\\", "/")


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _registry() -> dict[str, Any]:
    return _json(REGISTRY_PATH)


def test_proof_debt_lane_surface_selects_one_ledger_item() -> None:
    text = _read(SURFACE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        NEXT_TARGET,
        CONSUMED_TOKEN,
        RESULT_TOKEN,
        SELECTED_LANE,
        SELECTED_ITEM,
        SELECTED_DECLARATION,
        SELECTED_FILE,
        CURRENT_AUTHORITY,
        INTENDED_AUTHORITY,
        "ProofDebtLedgerDischargeLaneStatus",
        "ProofDebtLedgerDischargeLaneDecision",
        "selectDefaultNonAliasSpecBackedWitness",
        "proof_debt_ledger_discharge_lane_consumes_live_target_v0",
        "proof_debt_ledger_discharge_lane_consumes_selector_token_v0",
        "proof_debt_ledger_discharge_lane_exactly_one_item_v0",
        "proof_debt_ledger_discharge_lane_selected_item_v0",
        "proof_debt_ledger_discharge_lane_current_authority_v0",
        "proof_debt_ledger_discharge_lane_intended_authority_v0",
        "proof_debt_ledger_discharge_lane_result_token_v0",
        "proof_debt_ledger_discharge_lane_next_target_v0",
    }:
        assert token in text


def test_proof_debt_lane_surface_preserves_nonclaim_boundaries() -> None:
    text = _read(SURFACE_PATH)

    for theorem in {
        "proof_debt_ledger_discharge_lane_does_not_discharge_item_v0",
        "proof_debt_ledger_discharge_lane_no_pillar_completion_v0",
        "proof_debt_ledger_discharge_lane_no_seam_closure_v0",
        "proof_debt_ledger_discharge_lane_no_phase2_readiness_v0",
        "proof_debt_ledger_discharge_lane_no_empirical_claim_v0",
        "proof_debt_ledger_discharge_lane_master_action_not_promoted_v0",
    }:
        assert theorem in text


def test_proof_debt_lane_report_records_selected_item() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == "PROOF_DEBT_LEDGER_DISCHARGE_LANE_20260503_v0"
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["preparation_status"] == "completed_selection_only"
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_selector_token"] == CONSUMED_TOKEN
    assert report["selected_lane"] == SELECTED_LANE
    assert report["result_token"] == RESULT_TOKEN
    assert report["source_selector_surface"] == FULL_PILLAR_SELECTION_EVIDENCE
    assert report["source_selector_report"] == FULL_PILLAR_REPORT_EVIDENCE
    assert report["proof_debt_ledger"] == LEDGER_EVIDENCE
    assert report["preparation_surface"] == SURFACE_EVIDENCE
    assert report["focused_gate"] == (
        "formal/python/tests/test_proof_debt_ledger_discharge_lane_gate.py"
    )
    assert report["authorized_effect"] == "SELECT_EXACTLY_ONE_BOUNDED_PROOF_DEBT_ITEM"
    assert report["preparation_executes_discharge"] is False
    assert report["selected_item_count"] == 1
    assert report["selected_debt_item"] == SELECTED_ITEM
    assert report["selected_declaration"] == SELECTED_DECLARATION
    assert report["selected_file"] == SELECTED_FILE
    assert report["ledger_status"] == "spec_backed"
    assert report["current_authority"] == CURRENT_AUTHORITY
    assert report["intended_authority"] == INTENDED_AUTHORITY
    assert report["associated_pillar_or_seam"] == "SCALAR_QFT"
    assert report["blocks_full_pillar_target"] == "no"
    assert report["next_target"] == NEXT_TARGET
    assert not any(report["nonclaim_boundaries"].values())

    ledger = _read(LEDGER_PATH)
    assert f"| `{SELECTED_DECLARATION}` | `{SELECTED_FILE}` |" not in ledger
    assert f"| `sampleRep32` | `{SELECTED_FILE}` |" not in ledger


def test_registry_rotates_to_selected_proof_debt_item_execution() -> None:
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

    active = workstream(ACTIVE_LANE, payload)
    assert active["status"] == "active"
    assert active["authorization_evidence"] == RESULT_REVIEW_EVIDENCE
    assert active["authorized_next_slice"] == SELECTOR_SLICE
    assert active["authorized_next_strict_target"] == FINAL_TARGET
    assert active["consumed_target"] == REVIEW_TARGET
    assert active["latest_surface"] == RESULT_REVIEW_SURFACE_ID
    assert active["preparation_surface"] == SURFACE_EVIDENCE
    assert active["preparation_report"] == REPORT_EVIDENCE
    assert active["execution_surface"] == DISCHARGE_EVIDENCE
    assert active["execution_report"] == DISCHARGE_REPORT_EVIDENCE
    assert active["review_surface"] == RESULT_REVIEW_EVIDENCE
    assert active["review_report"] == RESULT_REVIEW_REPORT_EVIDENCE
    assert active["consumed_selection_token"] == CONSUMED_TOKEN
    assert active["preparation_result_token"] == RESULT_TOKEN
    assert active["discharge_result_token"] == DISCHARGE_RESULT_TOKEN
    assert active["result_token"] == REVIEW_RESULT_TOKEN
    assert active["selected_debt_item"] == SELECTED_ITEM
    assert active["selected_declaration"] == SELECTED_DECLARATION
    assert active["selected_file"] == SELECTED_FILE
    assert active["current_authority"] == CURRENT_AUTHORITY
    assert active["intended_authority"] == INTENDED_AUTHORITY
    assert active["debt_item_discharged"] == "yes"
    assert active["proof_debt_discharge_execution_authorized"] == (
        "completed_result_review_selector_selected"
    )
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

    assert NEXT_TARGET in payload["next_strict_target_coverage"]
    assert REVIEW_TARGET in payload["next_strict_target_coverage"]
    assert FINAL_TARGET in payload["next_strict_target_coverage"]
    assert "fnrep_nonalias_default_nonalias_discharge_result_review_nonclaim_boundary" in payload[
        "retained_blocker_coverage"
    ]


def test_public_surfaces_track_proof_debt_lane_preparation() -> None:
    for path in [
        README_PATH,
        STATE_PATH,
        ROADMAP_PATH,
        STRICT_MAP_PATH,
        SEAM_REGISTRY_PATH,
        SEAM_INVENTORY_PATH,
    ]:
        text = _read(path)
        assert NEXT_TARGET in text
        assert REVIEW_TARGET in text
        assert FINAL_TARGET in text
        assert SURFACE_EVIDENCE in text
        assert REPORT_EVIDENCE in text
        assert RESULT_TOKEN in text
        assert SELECTED_ITEM in text

    inventory = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-PROOF-DEBT-LEDGER-DISCHARGE-LANE-v0" in inventory
    assert SURFACE_EVIDENCE in inventory
    assert REPORT_EVIDENCE in inventory
    assert SELECTED_ITEM in inventory
    assert RESULT_TOKEN in inventory

    assert_focused_gate_not_manifest_enrolled(
        "test_proof_debt_ledger_discharge_lane_gate.py"
    )
