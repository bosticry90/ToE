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
    / "Variational"
    / "FNRepNonAliasEquivalence01SampleRep32DischargeResultReview.lean"
)
DISCHARGE_SURFACE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "FNRepNonAliasEquivalence01SampleRep32Discharge.lean"
)
SOURCE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "FNRepNonAliasEquivalence01.lean"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PROOF_DEBT_DISCHARGE_FNREP_SAMPLEREP32_RESULT_REVIEW_20260505_v0.json"
)
DISCHARGE_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PROOF_DEBT_DISCHARGE_FNREP_SAMPLEREP32_20260505_v0.json"
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

REVIEW_SURFACE_EVIDENCE = str(REVIEW_SURFACE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
DISCHARGE_SURFACE_EVIDENCE = str(DISCHARGE_SURFACE_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
SOURCE_EVIDENCE = str(SOURCE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
DISCHARGE_REPORT_EVIDENCE = str(DISCHARGE_REPORT_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
LEDGER_EVIDENCE = str(LEDGER_PATH.relative_to(REPO_ROOT)).replace("\\", "/")

SURFACE_ID = "fnrep_nonalias_samplerep32_discharge_result_review_v0"
CONSUMED_TARGET = "review_fnrep_nonalias_samplerep32_discharge_result"
NEXT_TARGET = "select_next_post_fnrep_samplerep32_discharge_bounded_attack"
CONSUMED_RESULT_TOKEN = "FNREP_NONALIAS_SAMPLEREP32_DISCHARGED_LEAN_BACKED_CONSTRUCTOR"
REVIEW_TOKEN = (
    "FNREP_NONALIAS_SAMPLEREP32_DISCHARGE_RESULT_REVIEW_CONSUMED_LEAN_BACKED_CONSTRUCTOR"
)
SELECTED_ITEM = f"{SOURCE_EVIDENCE}::sampleRep32"
ACTIVE_LANE = "fnrep_nonalias_samplerep32_discharge"
SELECTOR_SLICE = "post_fnrep_samplerep32_discharge_bounded_attack_selection_v0"
NONCLAIM_BOUNDARY = (
    "sampleRep32_result_review_consumed_pending_post_discharge_selection_no_promotion"
)
RECOMMENDED_SELECTOR_CHOICE = "prepare_axiom_ledger_audit_refresh"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _registry() -> dict[str, Any]:
    return _json(REGISTRY_PATH)


def test_sample_rep32_discharge_result_review_surface_consumes_result() -> None:
    text = _read(REVIEW_SURFACE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        NEXT_TARGET,
        REVIEW_TOKEN,
        RECOMMENDED_SELECTOR_CHOICE,
        "fnrepSampleRep32DischargeReviewConsumedResultTokenId",
        "FNRepSampleRep32DischargeResultReviewStatus",
        "FNRepSampleRep32DischargeResultReviewDecision",
        "consumeLeanBackedConstructorAndSelectPostDischargeSelector",
        "fnrep_samplerep32_discharge_result_review_consumes_live_target_v0",
        "fnrep_samplerep32_discharge_result_review_consumes_discharge_v0",
        "fnrep_samplerep32_discharge_result_review_item_discharged_v0",
        "fnrep_samplerep32_discharge_result_review_lean_backed_v0",
        "fnrep_samplerep32_discharge_result_review_axiom_removed_v0",
        "fnrep_samplerep32_discharge_result_review_ledger_row_removed_v0",
        "fnrep_samplerep32_discharge_result_review_default_nonalias_discharged_v0",
        "fnrep_samplerep32_discharge_result_review_axiom_count_v0",
        "fnrep_samplerep32_discharge_result_review_axiom_file_count_v0",
        "fnrep_samplerep32_discharge_result_review_token_v0",
        "fnrep_samplerep32_discharge_result_review_consumed_result_token_v0",
        "fnrep_samplerep32_discharge_result_review_selected_next_target_v0",
        "fnrep_samplerep32_discharge_result_review_decision_v0",
        "fnrep_samplerep32_discharge_result_review_recommends_audit_refresh_v0",
    }:
        assert token in text


def test_sample_rep32_discharge_result_review_preserves_nonclaim_boundaries() -> None:
    text = _read(REVIEW_SURFACE_PATH)

    for theorem in {
        "fnrep_samplerep32_discharge_result_review_qft_gr_not_authorized_v0",
        "fnrep_samplerep32_discharge_result_review_master_action_not_promoted_v0",
        "fnrep_samplerep32_discharge_result_review_no_pillar_completion_v0",
        "fnrep_samplerep32_discharge_result_review_no_seam_closure_v0",
        "fnrep_samplerep32_discharge_result_review_no_phase2_readiness_v0",
        "fnrep_samplerep32_discharge_result_review_no_empirical_claim_v0",
        "fnrep_samplerep32_discharge_result_review_no_canonical_toe_claim_v0",
        "fnrep_samplerep32_discharge_result_review_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_sample_rep32_discharge_result_review_report_confirms_ledger_state() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == (
        "PROOF_DEBT_DISCHARGE_FNREP_SAMPLEREP32_RESULT_REVIEW_20260505_v0"
    )
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["review_status"] == "completed_result_consumed"
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_result_token"] == CONSUMED_RESULT_TOKEN
    assert report["review_result_token"] == REVIEW_TOKEN
    assert report["review_surface"] == REVIEW_SURFACE_EVIDENCE
    assert report["discharge_surface"] == DISCHARGE_SURFACE_EVIDENCE
    assert report["discharge_report"] == DISCHARGE_REPORT_EVIDENCE
    assert report["proof_debt_ledger"] == LEDGER_EVIDENCE
    assert report["selected_debt_item"] == SELECTED_ITEM
    assert report["resulting_authority"] == (
        "LEAN_BACKED_EXPLICIT_SAMPLE_REPRESENTATION_CONSTRUCTOR"
    )
    assert report["review_effect"]["discharge_result_consumed"] is True
    assert report["review_effect"]["selected_item_confirmed_discharged"] is True
    assert report["review_effect"]["sample_rep32_lean_backed_constructor"] is True
    assert report["review_effect"]["sample_rep32_axiom_removed"] is True
    assert report["review_effect"]["sample_rep32_ledger_row_removed"] is True
    assert report["review_effect"]["default_nonalias_remains_discharged"] is True
    assert report["review_effect"]["ledger_count_after_discharge"] == 59
    assert report["review_effect"]["ledger_file_count_after_discharge"] == 14
    assert report["selected_next_target"] == NEXT_TARGET
    assert report["recommended_selector_choice"] == RECOMMENDED_SELECTOR_CHOICE
    assert report["review_executes_selector_choice"] is False
    assert not any(report["nonclaim_boundaries"].values())


def test_registry_rotates_to_post_sample_rep32_discharge_selector() -> None:
    payload = _registry()
    skip_if_not_current_target(payload, NEXT_TARGET)

    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_forbidden_promotions_closed()
    assert_public_surfaces_match_registry()
    state = payload["current_target_state"]

    assert state["previous_live_next_target"] == CONSUMED_TARGET
    assert state["live_next_target"] == NEXT_TARGET
    assert state["live_next_target_evidence"] == REVIEW_SURFACE_EVIDENCE
    assert state["active_lane"] == ACTIVE_LANE

    active = workstream(ACTIVE_LANE, payload)
    assert active["status"] == "active"
    assert active["retained_blocker"] == NONCLAIM_BOUNDARY
    assert active["authorization_evidence"] == REVIEW_SURFACE_EVIDENCE
    assert active["authorized_next_slice"] == SELECTOR_SLICE
    assert active["authorized_next_strict_target"] == NEXT_TARGET
    assert active["consumed_target"] == CONSUMED_TARGET
    assert active["latest_surface"] == SURFACE_ID
    assert active["execution_surface"] == DISCHARGE_SURFACE_EVIDENCE
    assert active["execution_report"] == DISCHARGE_REPORT_EVIDENCE
    assert active["review_surface"] == REVIEW_SURFACE_EVIDENCE
    assert active["review_report"] == REPORT_EVIDENCE
    assert active["proof_debt_ledger"] == LEDGER_EVIDENCE
    assert active["discharge_result_token"] == CONSUMED_RESULT_TOKEN
    assert active["consumed_result_token"] == CONSUMED_RESULT_TOKEN
    assert active["review_result_token"] == REVIEW_TOKEN
    assert active["result_token"] == REVIEW_TOKEN
    assert active["result_review_target"] == CONSUMED_TARGET
    assert active["selected_next_target"] == NEXT_TARGET
    assert active["recommended_selector_choice"] == RECOMMENDED_SELECTOR_CHOICE
    assert active["review_executes_selector_choice"] == "no"
    assert active["selected_debt_item"] == SELECTED_ITEM
    assert active["debt_item_discharged"] == "yes"
    assert active["axiom_removed"] == "yes"
    assert active["ledger_row_removed"] == "yes"
    assert active["real_axiom_count_after"] == 59
    assert active["real_axiom_file_count_after"] == 14
    assert active["default_nonalias_remains_discharged"] == "yes"
    assert active["pillar_completion_inferred"] == "no"
    assert active["seam_closure_claim"] == "no"
    assert active["phase2_readiness_claim"] == "no"
    assert active["empirical_adequacy_claim"] == "no"
    assert active["canonical_toe_claim"] == "no"
    assert active["qft_gr_source_map_closure_authorized"] == "no"
    assert active["master_action_promotion_authorized"] == "no"

    qft_gr = workstream("qft_gr_source_map", payload)
    assert qft_gr["authorized_next_strict_target"] == NEXT_TARGET
    assert qft_gr["full_source_map_closure_authorized"] == "no"

    master_action = workstream("master_action_dependency_frontier", payload)
    assert master_action["authorized_next_strict_target"] == NEXT_TARGET
    assert master_action["master_action_current_citation_target"] == NEXT_TARGET
    assert master_action["master_action_promotion_authorized"] == "no"

    assert NEXT_TARGET in payload["next_strict_target_coverage"]
    assert NONCLAIM_BOUNDARY in payload["retained_blocker_coverage"]
    edges = {
        (edge["from"], edge["to"], edge["evidence"])
        for edge in payload["dependency_edges"]
        if edge["status"] == "active"
    }
    assert (
        ACTIVE_LANE,
        "post_fnrep_samplerep32_discharge_bounded_attack_selection",
        REVIEW_SURFACE_EVIDENCE,
    ) in edges


def test_public_surfaces_track_sample_rep32_discharge_result_review() -> None:
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
        assert REVIEW_SURFACE_EVIDENCE in text
        assert REPORT_EVIDENCE in text
        assert REVIEW_TOKEN in text
        assert RECOMMENDED_SELECTOR_CHOICE in text

    inventory = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-PROOF-DEBT-DISCHARGE-FNREP-SAMPLEREP32-RESULT-REVIEW-v0" in inventory
    assert REVIEW_SURFACE_EVIDENCE in inventory
    assert REPORT_EVIDENCE in inventory
    assert REVIEW_TOKEN in inventory

    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_proof_debt_discharge_fnrep_samplerep32_result_review_gate.py"
    )
