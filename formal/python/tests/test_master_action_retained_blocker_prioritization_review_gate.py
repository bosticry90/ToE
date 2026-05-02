from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionRetainedBlockerPrioritizationReview.lean"
)
DEPENDENCY_GRAPH_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionDependencyGraphReview.lean"
)
AGGREGATE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
FRONTIER_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CrossPillarClosureFrontier.lean"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
GOVERNANCE_MANIFEST_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_TEST_MANIFEST_v1.json"
)
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

CONSUMED_TARGET = "prioritize_retained_blockers_after_master_action_dependency_graph_review"
LIVE_TARGET = "prepare_qm_stat_transport_semantics_retained_blocker_protocol_row"
SURFACE_ID = "master_action_retained_blocker_prioritization_review_v0"
TOP_BLOCKER = "PHASE1-BLOCKER-QMSTAT-TRANSPORT-RESIDUAL-PACKAGE-RETAINED"
REVIEW_EVIDENCE = str(REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _registry() -> dict[str, Any]:
    return json.loads(_read(REGISTRY_PATH))


def test_retained_blocker_prioritization_review_records_protocol_row_selection() -> None:
    text = _read(REVIEW_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        LIVE_TARGET,
        TOP_BLOCKER,
        "retainedBlockerPriorityIdsV0",
        "retained_blocker_prioritization_count_v0",
        "retained_blocker_prioritization_top_blocker_v0",
        "retained_blocker_prioritization_consumes_live_target_v0",
        "retained_blocker_prioritization_selected_next_target_v0",
        "retained_blocker_prioritization_frontier_target_v0",
        "retained_blocker_prioritization_completed_v0",
        "retained_blocker_prioritization_list_recorded_v0",
        "retained_blocker_prioritization_top_required_for_coherence_v0",
        "retained_blocker_prioritization_top_fatal_to_multiple_seams_v0",
        "retained_blocker_prioritization_protocol_row_only_v0",
    }:
        assert token in text


def test_retained_blocker_prioritization_preserves_fail_closed_boundaries() -> None:
    text = _read(REVIEW_PATH)

    for token in {
        "retained_blocker_prioritization_no_theorem_work_v0",
        "retained_blocker_prioritization_no_lane_unblocked_v0",
        "retained_blocker_prioritization_dependency_classes_unchanged_v0",
        "retained_blocker_prioritization_no_seam_closure_v0",
        "retained_blocker_prioritization_phase2_not_authorized_v0",
        "retained_blocker_prioritization_master_action_not_promoted_v0",
        "retained_blocker_prioritization_no_empirical_claim_v0",
        "retained_blocker_prioritization_governance_manifest_not_enrolled_v0",
    }:
        assert token in text


def test_frontier_and_aggregate_rotate_to_qm_stat_protocol_row_preparation() -> None:
    aggregate_text = _read(AGGREGATE_PATH)
    frontier_text = _read(FRONTIER_PATH)
    dependency_graph_text = _read(DEPENDENCY_GRAPH_REVIEW_PATH)

    assert "import ToeFormal.Derivation.MasterActionDependencyGraphReview" in aggregate_text
    assert (
        "import ToeFormal.Derivation.MasterActionRetainedBlockerPrioritizationReview"
        in aggregate_text
    )
    assert f'def previousLiveNextStrictTargetV0 : String :=\n  "{CONSUMED_TARGET}"' in frontier_text
    assert f'def currentLiveNextStrictTargetV0 : String :=\n  "{LIVE_TARGET}"' in frontier_text
    assert f'next_strict_slice :=\n        "{LIVE_TARGET}"' in frontier_text
    assert "master-action retained-blocker prioritization review" in frontier_text
    assert "retainedBlockerPrioritizationReviewTargetId" in dependency_graph_text


def test_loop_registry_tracks_prioritization_as_current_surface() -> None:
    payload = _registry()
    state = payload["current_target_state"]

    assert state["previous_live_next_target"] == CONSUMED_TARGET
    assert state["live_next_target"] == LIVE_TARGET
    assert state["live_next_target_evidence"] == REVIEW_EVIDENCE
    assert state["active_lane"] == "master_action_dependency_frontier"
    assert LIVE_TARGET in payload["next_strict_target_coverage"]

    active = [item for item in payload["workstreams"] if item.get("status") == "active"]
    assert [item["workstream_id"] for item in active] == ["master_action_dependency_frontier"]
    workstream = active[0]
    assert workstream["authorization_evidence"] == REVIEW_EVIDENCE
    assert workstream["consumed_target"] == CONSUMED_TARGET
    assert workstream["prior_consumed_target"] == (
        "review_master_action_dependency_graph_after_citation_language_audit"
    )
    assert workstream["prior_surface"] == "master_action_dependency_graph_review_v0"
    assert workstream["latest_surface"] == SURFACE_ID
    assert workstream["retained_blocker_prioritization_status"] == "completed"
    assert workstream["top_retained_blocker"] == TOP_BLOCKER
    assert workstream["top_retained_blocker_dependency_class"] == "required_for_coherence"
    assert workstream["top_retained_blocker_proof_debt_scope"] == "fatal_to_multiple_seams"
    assert workstream["next_action_scope"] == "protocol_row_preparation_only_no_theorem_work"
    assert workstream["theorem_work_authorized"] == "no"
    assert workstream["lane_unblocked"] == "no"
    assert workstream["dependency_classes_changed"] == "no"
    assert workstream["promotion_authorized"] == "no"
    assert workstream["authorized_next_strict_target"] == LIVE_TARGET
    assert workstream["same_lane_continuation"] == "protocol_row_preparation_only"

    edges = {(edge["from"], edge["to"]) for edge in payload["dependency_edges"]}
    assert (
        "master_action_dependency_graph_review",
        "master_action_retained_blocker_prioritization_review",
    ) in edges


def test_public_surfaces_expose_prioritization_and_manifest_remains_unchanged() -> None:
    for path in [README_PATH, STATE_PATH, ROADMAP_PATH, STRICT_MAP_PATH]:
        text = _read(path)
        assert LIVE_TARGET in text, f"{path} missing live target"
        assert (
            "retained-blocker prioritization" in text.lower()
            or "retained blocker prioritization" in text.lower()
            or "RETAINED_BLOCKER_PRIORITIZATION" in text
        ), f"{path} missing prioritization wording"

    for path in [STATE_PATH, STRICT_MAP_PATH, SEAM_REGISTRY_PATH, SEAM_INVENTORY_PATH]:
        assert "MasterActionRetainedBlockerPrioritizationReview.lean" in _read(path)

    inventory_text = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-MASTER-ACTION-RETAINED-BLOCKER-PRIORITIZATION-REVIEW-v0" in inventory_text
    assert REVIEW_EVIDENCE in inventory_text
    assert "test_master_action_retained_blocker_prioritization_review_gate.py" not in _read(
        GOVERNANCE_MANIFEST_PATH
    )
