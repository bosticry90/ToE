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
    / "PostRebaseNextBoundedAttackSelection.lean"
)
RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "FullPillarTargetMapRebaseResultReview.lean"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "POST_REBASE_NEXT_BOUNDED_ATTACK_SELECTION_20260503_v0.json"
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

SURFACE_ID = "post_rebase_next_bounded_attack_selection_v0"
PREVIOUS_TARGET = "review_full_pillar_target_map_rebase_result"
SELECTION_TARGET = "select_next_post_rebase_bounded_attack"
SELECTED_CLASS = "QFT_GR_SOURCE_MAP_CLOSURE_ELIGIBILITY_LANE"
SELECTED_TARGET = "prepare_qft_gr_state_expectation_functional_semantics_bounded_attack"
RESULT_REVIEW_TARGET = "review_qft_gr_state_expectation_functional_semantics_result"
LIVE_TARGET = "prepare_qft_gr_renormalized_expectation_value_semantics_bounded_attack"
REPORT_ID = "POST_REBASE_NEXT_BOUNDED_ATTACK_SELECTION_20260503_v0"
SELECTION_EVIDENCE = str(SELECTION_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
RESULT_REVIEW_EVIDENCE = str(RESULT_REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _registry() -> dict[str, Any]:
    return _json(REGISTRY_PATH)


def test_selection_lean_surface_records_exactly_one_bounded_class() -> None:
    text = _read(SELECTION_PATH)

    for token in {
        SURFACE_ID,
        SELECTION_TARGET,
        SELECTED_CLASS,
        SELECTED_TARGET,
        REPORT_EVIDENCE,
        "PostRebaseNextBoundedAttackSelectionStatus",
        "post_rebase_next_bounded_attack_selection_consumes_live_target_v0",
        "post_rebase_next_bounded_attack_selection_exactly_one_class_v0",
        "post_rebase_next_bounded_attack_selection_class_v0",
        "post_rebase_next_bounded_attack_selection_future_target_v0",
        "post_rebase_next_bounded_attack_selection_does_not_execute_attack_v0",
        "post_rebase_next_bounded_attack_selection_no_full_pillar_completion_v0",
        "post_rebase_next_bounded_attack_selection_no_seam_closure_v0",
        "post_rebase_next_bounded_attack_selection_phase2_not_authorized_v0",
        "post_rebase_next_bounded_attack_selection_master_action_not_promoted_v0",
        "post_rebase_next_bounded_attack_selection_no_empirical_claim_v0",
    }:
        assert token in text


def test_selection_report_has_one_selected_class_and_no_forbidden_effects() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["selection_target"] == SELECTION_TARGET
    assert report["current_target"] == PREVIOUS_TARGET
    assert report["review_result"] == "FULL_PILLAR_TARGET_MAP_REBASE_RESULT_REVIEW_CONSUMED"
    assert report["authorized_effect"] == "SELECT_EXACTLY_ONE_NEXT_BOUNDED_ATTACK"
    assert report["selection_executes_attack"] is False
    assert report["selected_class"] == SELECTED_CLASS
    assert report["selected_next_target"] == SELECTED_TARGET
    assert report["selected_next_target_kind"] == "preparation_only_before_theorem_attack"
    assert report["selection_count"] == 1

    selected = [row for row in report["candidate_classes"] if row["selection"] == "selected"]
    assert len(selected) == 1
    assert selected[0]["class_id"] == SELECTED_CLASS
    assert selected[0]["selected_next_target"] == SELECTED_TARGET
    assert selected[0]["selected_next_obligation"] == (
        "qft_state_expectation_functional_semantics"
    )

    forbidden = report["nonclaim_boundaries"]
    assert forbidden == {
        "full_pillar_completion_claim": False,
        "seam_closure_claim": False,
        "phase2_authorized": False,
        "master_action_promotion_authorized": False,
        "empirical_claim": False,
        "selection_executes_attack": False,
    }


def test_registry_rotates_to_selection_packet_without_attack_execution() -> None:
    assert_current_target_consistent()
    assert_frontier_matches_registry()
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
    assert "post_rebase_next_bounded_attack_selection" in state["paused_lanes"]

    review = workstream("full_pillar_target_map_rebase_result_review", payload)
    assert review["status"] == "paused"
    assert review["authorized_next_strict_target"] == SELECTION_TARGET
    assert review["selection_target"] == SELECTION_TARGET
    assert review["selection_surface"] == SELECTION_EVIDENCE
    assert review["selection_report"] == REPORT_EVIDENCE

    selection = workstream("post_rebase_next_bounded_attack_selection", payload)
    assert selection["status"] == "paused"
    assert selection["authorized_next_strict_target"] == SELECTED_TARGET
    assert selection["consumed_target"] == PREVIOUS_TARGET
    assert selection["latest_surface"] == SURFACE_ID
    assert selection["selection_surface"] == SELECTION_EVIDENCE
    assert selection["selection_report"] == REPORT_EVIDENCE
    assert selection["authorized_effect"] == "SELECT_EXACTLY_ONE_NEXT_BOUNDED_ATTACK"
    assert selection["candidate_class_count"] == 4
    assert selection["selection_count"] == 1
    assert selection["selected_class"] == SELECTED_CLASS
    assert selection["selected_source_row"] == "FULL_SEAM_QFT_GR_TARGET_MAP_v0"
    assert selection["selected_next_target"] == SELECTED_TARGET
    assert selection["selection_executes_attack"] == "no"
    assert selection["selection_status"] == "completed"
    assert selection["state_expectation_functional_result_review_target"] == RESULT_REVIEW_TARGET
    assert selection["theorem_work_authorized"] == (
        "bounded_expectation_functional_semantics_completed_result_review_only"
    )

    assert SELECTION_TARGET in payload["next_strict_target_coverage"]
    assert SELECTED_TARGET in payload["next_strict_target_coverage"]
    assert LIVE_TARGET in payload["next_strict_target_coverage"]
    edges = {(edge["from"], edge["to"]) for edge in payload["dependency_edges"]}
    assert (
        "full_pillar_target_map_rebase_result_review",
        "post_rebase_next_bounded_attack_selection",
    ) in edges


def test_public_surfaces_and_inventory_track_selection_packet() -> None:
    for path in [README_PATH, STATE_PATH, ROADMAP_PATH, STRICT_MAP_PATH]:
        text = _read(path)
        assert LIVE_TARGET in text
        assert RESULT_REVIEW_TARGET in text
        assert SELECTED_TARGET in text
        assert "PostRebaseNextBoundedAttackSelection.lean" in text

    for path in [SEAM_REGISTRY_PATH, SEAM_INVENTORY_PATH]:
        text = _read(path)
        assert LIVE_TARGET in text
        assert RESULT_REVIEW_TARGET in text
        assert SELECTED_CLASS in text
        assert SELECTED_TARGET in text
        assert "PostRebaseNextBoundedAttackSelection.lean" in text

    inventory_text = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-POST-REBASE-NEXT-BOUNDED-ATTACK-SELECTION-v0" in inventory_text
    assert SELECTION_EVIDENCE in inventory_text
    assert REPORT_EVIDENCE in inventory_text
    assert SELECTED_CLASS in inventory_text
    assert SELECTED_TARGET in inventory_text

    assert_focused_gate_not_manifest_enrolled(
        "test_post_rebase_next_bounded_attack_selection_gate.py"
    )
