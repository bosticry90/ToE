from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
)
from formal.python.tools.post_toe_expert_translation_bounded_target_selection_report import (
    ALLOWED_OUTCOME_CATEGORIES,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    OUTCOME_CATEGORY,
    OUTCOME_ID,
    SELECTED_NEXT_TARGET,
    build_selection,
)
from formal.python.tools.qft_gr_minimal_working_model_demonstration_packet_report import (
    REVIEW_TARGET as MINIMAL_MODEL_PACKET_REVIEW_TARGET,
)


REPO_ROOT = find_repo_root(Path(__file__))
LEAN_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostTOEExpertTranslationBoundedTargetSelection.lean"
)
TOE_FORMAL_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
V01_INDEX_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
FRONTIER_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CrossPillarClosureFrontier.lean"
)
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
STRICT_MAP_PATH = (
    REPO_ROOT / "formal" / "docs" / "lanes" / "STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md"
)
SEAM_REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md"
)
SEAM_INVENTORY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _workstream(payload: dict, workstream_id: str) -> dict:
    for item in payload["workstreams"]:
        if item["workstream_id"] == workstream_id:
            return item
    raise AssertionError(f"Missing workstream: {workstream_id}")


def test_post_translation_selection_is_deterministic_and_bounded() -> None:
    payload = _json(DEFAULT_OUT)
    assert payload == build_selection()
    assert payload["consumed_target"] == CONSUMED_TARGET
    assert payload["outcome_category"] == OUTCOME_CATEGORY
    assert payload["allowed_outcome_categories"] == ALLOWED_OUTCOME_CATEGORIES
    assert payload["outcome_id"] == OUTCOME_ID
    assert payload["selected_next_target"] == SELECTED_NEXT_TARGET
    assert payload["selection_count"] == 1
    assert payload["next_assumption_family_authorized"] is False
    assert payload["public_theory_readiness_claimed"] is False
    assert payload["release_or_public_submission_authorized"] is False
    assert payload["bounded_handoff_requires_review"] is True
    for value in payload["acceptance_criteria"].values():
        assert value is True
    for key, value in payload["non_claim_boundary"].items():
        assert value is False, key


def test_post_translation_selection_updates_authoritative_live_target() -> None:
    registry = _json(REGISTRY_PATH)
    state = registry["current_target_state"]

    assert SELECTED_NEXT_TARGET in registry["next_strict_target_coverage"]
    assert CONSUMED_TARGET in registry["next_strict_target_coverage"]
    assert state["previous_live_next_target"] in {
        CONSUMED_TARGET,
        SELECTED_NEXT_TARGET,
        "execute_qft_gr_minimal_working_model_construction_attempt",
        "review_qft_gr_minimal_working_model_construction_attempt_result",
    }
    assert state["live_next_target"] in {
        SELECTED_NEXT_TARGET,
        MINIMAL_MODEL_PACKET_REVIEW_TARGET,
        "review_qft_gr_minimal_working_model_construction_attempt_result",
        "analyze_qft_gr_minimal_working_model_candidate_only",
    }

    consumed_selector = _workstream(registry, CONSUMED_TARGET)
    assert consumed_selector["status"] == "paused"
    assert consumed_selector["selected_next_target"] == SELECTED_NEXT_TARGET
    assert consumed_selector["outcome_category"] == OUTCOME_CATEGORY

    minimal_model_packet = _workstream(registry, SELECTED_NEXT_TARGET)
    assert minimal_model_packet["status"] in {"active", "paused"}
    assert minimal_model_packet["authorized_next_strict_target"] in {
        SELECTED_NEXT_TARGET,
        MINIMAL_MODEL_PACKET_REVIEW_TARGET,
    }


def test_post_translation_selection_has_lean_and_public_surface_mirrors() -> None:
    joined = "\n".join(
        _read(path)
        for path in [
            LEAN_PATH,
            TOE_FORMAL_PATH,
            V01_INDEX_PATH,
            REGISTRY_PATH,
            SURFACES_PATH,
            ROADMAP_PATH,
            FRONTIER_PATH,
            README_PATH,
            STATE_PATH,
            STRICT_MAP_PATH,
            SEAM_REGISTRY_PATH,
            SEAM_INVENTORY_PATH,
        ]
    )
    for token in [
        "POST_TOE_EXPERT_TRANSLATION_BOUNDED_TARGET_SELECTION_v0",
        OUTCOME_ID,
        OUTCOME_CATEGORY,
        CONSUMED_TARGET,
        SELECTED_NEXT_TARGET,
        "no QFT-GR closure",
        "no public submission",
    ]:
        assert token in joined

    frontier = _read(FRONTIER_PATH)
    assert SELECTED_NEXT_TARGET in frontier


def test_post_translation_selection_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_post_toe_expert_translation_bounded_target_selection_gate.py"
    )
