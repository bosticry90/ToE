from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_current_target_consistent,
    assert_focused_gate_not_manifest_enrolled,
    assert_forbidden_promotions_closed,
    assert_public_surfaces_match_registry,
    skip_if_not_current_target,
    workstream,
)


REPO_ROOT = find_repo_root(Path(__file__))
REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "FullPillarTargetMapRebaseResultReview.lean"
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
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "FULL_PILLAR_TARGET_MAP_REBASE_RESULT_REVIEW_20260503_v0.json"
)
LEDGER_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LEAN_AXIOM_SPEC_BACKED_LEDGER_v0.md"
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

SURFACE_ID = "full_pillar_target_map_rebase_result_review_v0"
CONSUMED_TARGET = "prepare_full_pillar_target_map_rebase"
REVIEW_TARGET = "review_full_pillar_target_map_rebase_result"
SELECTION_TARGET = "select_next_post_rebase_bounded_attack"
SELECTED_TARGET = "prepare_qft_gr_state_expectation_functional_semantics_bounded_attack"
RESULT_REVIEW_TARGET = "review_qft_gr_state_expectation_functional_semantics_result"
LIVE_TARGET = "prepare_qft_gr_renormalized_expectation_value_semantics_bounded_attack"
REPORT_ID = "FULL_PILLAR_TARGET_MAP_REBASE_RESULT_REVIEW_20260503_v0"
TARGET_MAP_ID = "FULL_PILLAR_TARGET_MAP_REBASE_v0"
ACCEPTANCE_CONDITION = (
    "target_map_confirmed_as_navigation_eligibility_and_proof_debt_authority_only"
)
REVIEW_EVIDENCE = str(REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
TARGET_MAP_EVIDENCE = str(TARGET_MAP_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
TARGET_MAP_DOC_EVIDENCE = str(TARGET_MAP_DOC_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
LEDGER_EVIDENCE = str(LEDGER_PATH.relative_to(REPO_ROOT)).replace("\\", "/")


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _registry() -> dict[str, Any]:
    return _json(REGISTRY_PATH)


def test_result_review_lean_surface_records_nonclaim_review_packet() -> None:
    text = _read(REVIEW_PATH)

    for token in {
        SURFACE_ID,
        SELECTION_TARGET,
        REPORT_EVIDENCE,
        "FullPillarTargetMapRebaseResultReviewStatus",
        "fullPillarTargetMapRebaseResultReviewConsumedTargetId",
        "full_pillar_target_map_rebase_result_review_consumes_live_target_v0",
        "full_pillar_target_map_rebase_result_review_packet_recorded_v0",
        "full_pillar_target_map_rebase_result_review_internal_sync_confirmed_v0",
        "full_pillar_target_map_rebase_result_review_no_unauthorized_claims_v0",
        "full_pillar_target_map_rebase_result_review_proof_debt_ledger_attached_v0",
        "full_pillar_target_map_rebase_result_review_no_next_attack_selected_v0",
        "full_pillar_target_map_rebase_result_review_phase2_not_authorized_v0",
        "full_pillar_target_map_rebase_result_review_no_seam_closure_claim_v0",
        "full_pillar_target_map_rebase_result_review_no_full_pillar_completion_v0",
        "full_pillar_target_map_rebase_result_review_master_action_not_promoted_v0",
        "full_pillar_target_map_rebase_result_review_no_empirical_claim_v0",
    }:
        assert token in text


def test_result_review_report_preserves_authority_only_acceptance_condition() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["review_status"] == "prepared_for_live_result_review"
    assert report["consumed_target"] == CONSUMED_TARGET
    assert report["live_next_target"] == REVIEW_TARGET
    assert report["review_surface"] == REVIEW_EVIDENCE
    assert report["target_map_surface"] == TARGET_MAP_EVIDENCE
    assert report["target_map_document"] == TARGET_MAP_DOC_EVIDENCE
    assert report["axiom_spec_backed_ledger"] == LEDGER_EVIDENCE
    assert report["acceptance_condition"] == ACCEPTANCE_CONDITION

    findings = report["findings"]
    for forbidden_key in {
        "unauthorized_claims_introduced",
        "full_pillar_completion_claim",
        "seam_closure_claim",
        "phase2_authorized",
        "empirical_claim",
        "master_action_promotion_authorized",
        "new_physics_progress_claim",
        "next_physics_attack_selected",
    }:
        assert findings[forbidden_key] is False
    for required_key in {
        "all_rows_have_route_source",
        "all_rows_have_completion_scale",
        "all_rows_have_claim_posture",
        "local_rows_not_promoted_to_pillar_completion",
        "open_pillar_rows_name_missing_full_target",
        "supplied_routes_name_supplied_object",
        "master_action_citation_bound",
        "live_target_represented_by_rebase_selection",
    }:
        assert findings[required_key] is True

    assert report["row_summary"]["target_map_row_count"] == 13
    assert report["row_summary"]["master_action_row"] == "MASTER_ACTION_FULL_DEPENDENCY_MAP_v0"
    assert report["proof_debt_summary"] == {
        "real_axiom_count": 61,
        "real_sorry_or_admit_count": 0,
        "real_axiom_file_count": 15,
        "ledger_status": "attached_to_result_review_packet",
    }
    assert "next_physics_attack_before_result_review_decision" in report["not_authorized"]


def test_registry_rotates_to_target_map_result_review_only() -> None:
    assert_current_target_consistent()
    assert_forbidden_promotions_closed()
    assert_public_surfaces_match_registry()
    payload = _registry()
    skip_if_not_current_target(payload, LIVE_TARGET)
    state = payload["current_target_state"]

    assert state["previous_live_next_target"] == RESULT_REVIEW_TARGET
    assert state["live_next_target"] == LIVE_TARGET
    assert (
        state["active_lane"]
        == "qft_gr_renormalized_expectation_value_semantics_preparation"
    )

    target_map = workstream("full_pillar_target_map_rebase", payload)
    assert target_map["status"] == "paused"
    assert target_map["target_map_result_review_target"] == REVIEW_TARGET
    assert target_map["target_map_result_review_surface"] == REVIEW_EVIDENCE
    assert target_map["target_map_result_review_report"] == REPORT_EVIDENCE
    assert target_map["target_map_result_review_status"] == "prepared_for_live_result_review"
    assert target_map["theorem_work_authorized"] == "result_review_only_after_target_map_rebase"

    review = workstream("full_pillar_target_map_rebase_result_review", payload)
    assert review["status"] == "paused"
    assert review["authorized_next_strict_target"] == SELECTION_TARGET
    assert review["consumed_target"] == CONSUMED_TARGET
    assert review["latest_surface"] == SURFACE_ID
    assert review["review_surface"] == REVIEW_EVIDENCE
    assert review["release_report"] == REPORT_EVIDENCE
    assert review["target_map_evidence"] == TARGET_MAP_EVIDENCE
    assert review["target_map_document"] == TARGET_MAP_DOC_EVIDENCE
    assert review["axiom_spec_backed_ledger"] == LEDGER_EVIDENCE
    assert review["review_packet_status"] == "prepared_for_live_result_review"
    assert review["target_map_authority_only"] == "yes"
    assert review["unauthorized_claims_introduced"] == "no"
    assert review["full_pillar_completion_claim"] == "no"
    assert review["seam_closure_claim"] == "no"
    assert review["phase2_authorized"] == "no"
    assert review["empirical_claim"] == "no"
    assert review["master_action_promotion_authorized"] == "no"
    assert review["next_physics_attack_selected"] == "no"
    assert review["theorem_work_authorized"] == "selection_only_no_physics_attack"
    assert review["selection_target"] == SELECTION_TARGET

    selection = workstream("post_rebase_next_bounded_attack_selection", payload)
    assert selection["status"] == "paused"
    assert selection["authorized_next_strict_target"] == SELECTED_TARGET
    assert selection["selected_next_target"] == SELECTED_TARGET
    assert selection["selection_executes_attack"] == "no"

    edges = {(edge["from"], edge["to"]) for edge in payload["dependency_edges"]}
    assert ("full_pillar_target_map_rebase", "full_pillar_target_map_rebase_result_review") in edges


def test_public_surfaces_and_inventory_track_result_review_packet() -> None:
    for path in [README_PATH, STATE_PATH, ROADMAP_PATH, STRICT_MAP_PATH]:
        text = _read(path)
        assert LIVE_TARGET in text
        assert RESULT_REVIEW_TARGET in text
        assert SELECTED_TARGET in text
        if path in {ROADMAP_PATH, STRICT_MAP_PATH}:
            assert SELECTION_TARGET in text
        if path in {ROADMAP_PATH, STRICT_MAP_PATH}:
            assert CONSUMED_TARGET in text
        assert "FullPillarTargetMapRebaseResultReview.lean" in text
        if path != README_PATH:
            assert REPORT_ID in text or REPORT_EVIDENCE in text

    for path in [SEAM_REGISTRY_PATH, SEAM_INVENTORY_PATH]:
        text = _read(path)
        assert LIVE_TARGET in text
        assert RESULT_REVIEW_TARGET in text
        assert SELECTED_TARGET in text
        assert "FullPillarTargetMapRebaseResultReview.lean" in text
        assert REPORT_ID in text or REPORT_EVIDENCE in text

    inventory_text = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-FULL-PILLAR-TARGET-MAP-REBASE-RESULT-REVIEW-v0" in inventory_text
    assert REVIEW_EVIDENCE in inventory_text
    assert REPORT_EVIDENCE in inventory_text
    assert TARGET_MAP_ID in inventory_text

    assert_focused_gate_not_manifest_enrolled(
        "test_full_pillar_target_map_rebase_result_review_gate.py"
    )
