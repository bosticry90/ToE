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
    current_target_state,
)


REPO_ROOT = find_repo_root(Path(__file__))
REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionPostQMSTATRetainedBlockerPrioritizationReview.lean"
)
SOURCE_PROBABILITY_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMSTATSourceProbabilityExtractionResultReview.lean"
)
QFT_GR_SOURCE_MAP_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_StressEnergyExpectationSourceMap.lean"
)
QFT_GR_POST_BUDGET_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRPostBudgetCrossPillarReview.lean"
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

CONSUMED_TARGET = "prioritize_retained_blockers_after_qm_stat_source_probability_result_review"
QFT_GR_PROTOCOL_PREPARATION_TARGET = (
    "prepare_qft_gr_source_map_semantics_retained_blocker_protocol_row"
)
LIVE_TARGET = current_target_state()["live_next_target"]
SURFACE_ID = "master_action_post_qm_stat_retained_blocker_prioritization_review_v0"
TOP_BLOCKER = "PHASE1-BLOCKER-QFTGR-STRESS-ENERGY-EXPECTATION-SOURCE-MAP-RETAINED"
REVIEW_EVIDENCE = str(REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _registry() -> dict[str, Any]:
    return json.loads(_read(REGISTRY_PATH))


def _workstream(payload: dict[str, Any], workstream_id: str) -> dict[str, Any]:
    for item in payload["workstreams"]:
        if item["workstream_id"] == workstream_id:
            return item
    raise AssertionError(f"Missing workstream: {workstream_id}")


def test_post_qm_stat_prioritization_surface_records_qft_gr_protocol_selection() -> None:
    text = _read(REVIEW_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        QFT_GR_PROTOCOL_PREPARATION_TARGET,
        TOP_BLOCKER,
        "postQMSTATRetainedBlockerPriorityIdsV0",
        "post_qm_stat_retained_blocker_prioritization_count_v0",
        "post_qm_stat_retained_blocker_prioritization_top_blocker_v0",
        "post_qm_stat_retained_blocker_prioritization_consumes_live_target_v0",
        "post_qm_stat_retained_blocker_prioritization_selected_next_target_v0",
        "post_qm_stat_retained_blocker_prioritization_frontier_target_v0",
        "post_qm_stat_retained_blocker_prioritization_completed_v0",
        "post_qm_stat_retained_blocker_prioritization_list_recorded_v0",
        "post_qm_stat_retained_blocker_prioritization_top_required_v0",
        "post_qm_stat_retained_blocker_prioritization_top_fatal_v0",
        "post_qm_stat_retained_blocker_prioritization_protocol_row_only_v0",
    }:
        assert token in text


def test_post_qm_stat_prioritization_preserves_fail_closed_boundaries() -> None:
    text = _read(REVIEW_PATH)

    for token in {
        "post_qm_stat_retained_blocker_prioritization_qm_stat_paused_v0",
        "post_qm_stat_retained_blocker_prioritization_no_theorem_work_v0",
        "post_qm_stat_retained_blocker_prioritization_no_lane_unblocked_v0",
        "post_qm_stat_retained_blocker_prioritization_dependency_classes_unchanged_v0",
        "post_qm_stat_retained_blocker_prioritization_no_qft_gr_seam_closure_v0",
        "post_qm_stat_retained_blocker_prioritization_no_semiclassical_gravity_claim_v0",
        "post_qm_stat_retained_blocker_prioritization_no_einstein_equation_claim_v0",
        "post_qm_stat_retained_blocker_prioritization_phase2_not_authorized_v0",
        "post_qm_stat_retained_blocker_prioritization_master_action_not_promoted_v0",
        "post_qm_stat_retained_blocker_prioritization_no_empirical_claim_v0",
        "post_qm_stat_retained_blocker_prioritization_governance_manifest_not_enrolled_v0",
    }:
        assert token in text


def test_frontier_and_aggregate_rotate_to_qft_gr_protocol_row_preparation() -> None:
    assert_frontier_matches_registry()

    aggregate_text = _read(AGGREGATE_PATH)
    frontier_text = _read(FRONTIER_PATH)

    assert (
        "import ToeFormal.Derivation.MasterActionPostQMSTATRetainedBlockerPrioritizationReview"
        in aggregate_text
    )
    assert f'def currentLiveNextStrictTargetV0 : String :=\n  "{LIVE_TARGET}"' in frontier_text
    assert f'next_strict_slice :=\n        "{LIVE_TARGET}"' in frontier_text


def test_loop_registry_tracks_post_qm_stat_prioritization_as_current_surface() -> None:
    assert_current_target_consistent()
    assert_forbidden_promotions_closed()

    payload = _registry()
    skip_if_not_current_target(payload, QFT_GR_PROTOCOL_PREPARATION_TARGET)
    state = payload["current_target_state"]
    master_action = _workstream(payload, "master_action_dependency_frontier")
    qft_gr = _workstream(payload, "qft_gr_source_map")
    qm_stat = _workstream(payload, "qm_stat_transport_residual")

    assert state["live_next_target"] == LIVE_TARGET
    assert state["active_lane"] == "qft_gr_source_map"

    assert master_action["post_qm_stat_retained_blocker_prioritization_status"] == "completed"
    assert master_action["post_qm_stat_top_retained_blocker"] == TOP_BLOCKER
    assert (
        master_action["qft_gr_source_map_protocol_row_preparation_target"]
        == QFT_GR_PROTOCOL_PREPARATION_TARGET
    )
    assert master_action["qft_gr_source_map_protocol_row_status"] == "prepared"

    assert qft_gr["status"] in {"active", "paused"}
    assert qft_gr["protocol_row_preparation_target"] == QFT_GR_PROTOCOL_PREPARATION_TARGET
    assert qft_gr["protocol_row_preparation_authorized"] == "preparation_only_no_theorem_work"
    assert qft_gr["readiness_review_status"] == "completed"
    assert qft_gr["authorized_next_strict_target"] == LIVE_TARGET

    assert qm_stat["status"] == "paused"
    assert qm_stat["source_probability_result_review_status"] == "completed"
    assert qm_stat["target_entropy_semantics_authorized"] == "no"
    assert qm_stat["transport_map_semantics_authorized"] == "no"

    assert QFT_GR_PROTOCOL_PREPARATION_TARGET in payload["next_strict_target_coverage"]
    assert LIVE_TARGET in payload["next_strict_target_coverage"]
    edges = {(edge["from"], edge["to"]) for edge in payload["dependency_edges"]}
    assert (
        "qm_stat_retained_blocker_prioritization_after_source_probability_result",
        "qft_gr_source_map_semantics_retained_blocker_protocol_row",
    ) in edges


def test_public_surfaces_expose_post_qm_stat_prioritization() -> None:
    assert_public_surfaces_match_registry()

    for path in [README_PATH, STATE_PATH, ROADMAP_PATH, STRICT_MAP_PATH]:
        text = _read(path)
        assert "MasterActionPostQMSTATRetainedBlockerPrioritizationReview.lean" in text
        assert TOP_BLOCKER in text

    for path in [SEAM_REGISTRY_PATH, SEAM_INVENTORY_PATH]:
        text = _read(path)
        assert "MASTER_ACTION_POST_QMSTAT_RETAINED_BLOCKER_PRIORITIZATION" in text
        assert QFT_GR_PROTOCOL_PREPARATION_TARGET in text

    inventory_text = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert (
        "INV-MATH-MASTER-ACTION-POST-QMSTAT-RETAINED-BLOCKER-PRIORITIZATION-REVIEW-v0"
        in inventory_text
    )
    assert REVIEW_EVIDENCE in inventory_text
    assert_focused_gate_not_manifest_enrolled(
        "test_master_action_post_qm_stat_retained_blocker_prioritization_review_gate.py"
    )


def test_source_probability_and_qft_gr_inputs_remain_bounded() -> None:
    source_probability_review_text = _read(SOURCE_PROBABILITY_RESULT_REVIEW_PATH)
    qft_gr_source_map_text = _read(QFT_GR_SOURCE_MAP_PATH)
    qft_gr_review_text = _read(QFT_GR_POST_BUDGET_REVIEW_PATH)

    assert "qm_stat_source_probability_result_review_same_lane_not_authorized_v0" in (
        source_probability_review_text
    )
    assert "qft_gr_stress_energy_source_map_retained_blocker_id_v0" in qft_gr_source_map_text
    assert "qft_gr_post_budget_same_lane_not_authorized_v0" in qft_gr_review_text
    assert "qft_gr_post_budget_no_semiclassical_gravity_claim_v0" in qft_gr_review_text
