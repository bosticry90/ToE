from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_current_target_consistent,
    assert_focused_gate_not_manifest_enrolled,
    assert_frontier_matches_registry,
    assert_public_surfaces_match_registry,
    current_target_state,
    workstream,
)


REPO_ROOT = find_repo_root(Path(__file__))
RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMSTATSourceProbabilityExtractionResultReview.lean"
)
SOURCE_PROBABILITY_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QM_STAT_SourceProbabilityExtractionSemantics.lean"
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

CONSUMED_TARGET = "review_qm_stat_source_probability_extraction_semantics_result"
NEXT_TARGET = "prioritize_retained_blockers_after_qm_stat_source_probability_result_review"
LIVE_TARGET = current_target_state()["live_next_target"]
RESULT_REVIEW_EVIDENCE = str(RESULT_REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
SOURCE_PROBABILITY_EVIDENCE = str(
    SOURCE_PROBABILITY_PATH.relative_to(REPO_ROOT)
).replace("\\", "/")
SURFACE_ID = "qm_stat_source_probability_extraction_result_review_v0"
SOURCE_SURFACE_ID = "QM_STAT_SOURCE_PROBABILITY_EXTRACTION_SEMANTICS_v0"
DECISION_ID = "pause_qm_stat_and_prioritize_retained_blockers"
RETAINED_BLOCKER = (
    "PHASE1-BLOCKER-QMSTAT-SOURCE-PROBABILITY-EXTRACTION-SEMANTICS-RETAINED"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _registry() -> dict[str, Any]:
    return json.loads(_read(REGISTRY_PATH))


def test_result_review_records_bounded_pause_decision() -> None:
    text = _read(RESULT_REVIEW_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        NEXT_TARGET,
        DECISION_ID,
        "QMSTATSourceProbabilityExtractionResultReviewStatus",
        "qm_stat_source_probability_result_review_completed_v0",
        "qm_stat_source_probability_result_review_accepts_supplied_route_v0",
        "qm_stat_source_probability_result_review_contract_only_refuted_v0",
        "qm_stat_source_probability_result_review_retained_as_supplied_v0",
        "qm_stat_source_probability_result_review_selected_decision_v0",
        "qm_stat_source_probability_result_review_selected_next_target_v0",
        "qm_stat_source_probability_result_review_frontier_target_v0",
        "qm_stat_source_probability_result_review_same_lane_not_authorized_v0",
        "qm_stat_source_probability_result_review_dependency_graph_unchanged_v0",
        "qm_stat_source_probability_result_review_no_lane_unblocked_v0",
    }:
        assert token in text

    source_text = _read(SOURCE_PROBABILITY_PATH)
    assert "qm_stat_source_probability_extraction_supplied_route_available_v0" in source_text
    assert "qm_stat_source_probability_extraction_contract_only_refuted_v0" in source_text


def test_result_review_preserves_fail_closed_boundaries() -> None:
    text = _read(RESULT_REVIEW_PATH)

    for theorem in {
        "qm_stat_source_probability_result_review_no_broader_theorem_work_v0",
        "qm_stat_source_probability_result_review_target_entropy_not_authorized_v0",
        "qm_stat_source_probability_result_review_transport_map_not_authorized_v0",
        "qm_stat_source_probability_result_review_coarse_graining_not_authorized_v0",
        "qm_stat_source_probability_result_review_residual_closure_not_authorized_v0",
        "qm_stat_source_probability_result_review_no_seam_closure_v0",
        "qm_stat_source_probability_result_review_no_stat_mechanics_claim_v0",
        "qm_stat_source_probability_result_review_phase2_not_authorized_v0",
        "qm_stat_source_probability_result_review_master_action_not_promoted_v0",
        "qm_stat_source_probability_result_review_no_empirical_claim_v0",
        "qm_stat_source_probability_result_review_governance_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_frontier_and_aggregate_rotate_to_retained_blocker_prioritization() -> None:
    assert_frontier_matches_registry()
    aggregate_text = _read(AGGREGATE_PATH)
    frontier_text = _read(FRONTIER_PATH)

    assert (
        "import ToeFormal.Derivation.QMSTATSourceProbabilityExtractionResultReview"
        in aggregate_text
    )
    assert "source-probability result review and same-lane pause" in frontier_text
    assert "source-probability result review and same-lane pause" in frontier_text
    assert NEXT_TARGET in frontier_text


def test_loop_registry_tracks_result_review_and_pauses_qm_stat() -> None:
    assert_current_target_consistent()
    payload = _registry()

    qm_stat = workstream("qm_stat_transport_residual", payload)
    assert qm_stat["status"] == "paused"
    assert qm_stat["retained_blocker"] == RETAINED_BLOCKER
    assert qm_stat["source_probability_extraction_semantics_status"] == (
        "supplied_route_available_contract_only_refuted_retained_as_semantic_assumption"
    )
    assert qm_stat["source_probability_result_review_status"] == "completed"
    assert qm_stat["source_probability_result_review_evidence"] == RESULT_REVIEW_EVIDENCE
    assert qm_stat["source_probability_result_review_decision"] == DECISION_ID
    assert qm_stat["authorized_next_strict_target"] == NEXT_TARGET
    assert qm_stat["same_lane_continuation"] == (
        "not_authorized_after_source_probability_result_review"
    )
    assert qm_stat["theorem_work_authorized"] == "no_result_review_completed_same_lane_paused"
    assert qm_stat["target_entropy_semantics_authorized"] == "no"
    assert qm_stat["transport_map_semantics_authorized"] == "no"
    assert qm_stat["coarse_graining_irreversibility_authorized"] == "no"
    assert qm_stat["residual_package_semantic_closure_authorized"] == "no"

    master_action = workstream("master_action_dependency_frontier", payload)
    assert master_action["status"] == "paused"
    assert master_action["source_probability_extraction_evidence"] == SOURCE_PROBABILITY_EVIDENCE
    assert master_action["source_probability_result_review_status"] == "completed"
    assert master_action["source_probability_result_review_decision"] == DECISION_ID
    assert master_action["dependency_graph_changed"] == "no"
    assert master_action["lane_unblocked"] == "no"
    assert master_action["promotion_authorized"] == "no"

    edges = {(edge["from"], edge["to"]) for edge in payload["dependency_edges"]}
    assert (
        "qm_stat_source_probability_extraction_semantics",
        "qm_stat_source_probability_extraction_semantics_result_review",
    ) in edges
    assert (
        "qm_stat_source_probability_extraction_semantics_result_review",
        "qm_stat_retained_blocker_prioritization_after_source_probability_result",
    ) in edges


def test_public_surfaces_and_manifest_boundary_are_synchronized() -> None:
    assert_public_surfaces_match_registry()

    for path in [README_PATH, STATE_PATH, ROADMAP_PATH, STRICT_MAP_PATH]:
        text = _read(path)
        assert "QMSTATSourceProbabilityExtractionResultReview.lean" in text

    for path in [STATE_PATH, ROADMAP_PATH, STRICT_MAP_PATH]:
        text = _read(path)
        assert NEXT_TARGET in text

    for path in [SEAM_REGISTRY_PATH, SEAM_INVENTORY_PATH]:
        text = _read(path)
        assert "QM_STAT_SOURCE_PROBABILITY_RESULT_REVIEW_STATUS_v0" in text
        assert NEXT_TARGET in text

    inventory_text = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-QMSTAT-SOURCE-PROBABILITY-RESULT-REVIEW-v0" in inventory_text
    assert RESULT_REVIEW_EVIDENCE in inventory_text
    assert SOURCE_SURFACE_ID in inventory_text
    assert_focused_gate_not_manifest_enrolled(
        "test_qm_stat_source_probability_result_review_gate.py"
    )
