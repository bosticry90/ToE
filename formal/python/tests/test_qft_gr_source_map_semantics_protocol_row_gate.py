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
)


REPO_ROOT = find_repo_root(Path(__file__))
PROTOCOL_ROW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRSourceMapSemanticsRetainedBlockerProtocolRow.lean"
)
POST_QMSTAT_PRIORITIZATION_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionPostQMSTATRetainedBlockerPrioritizationReview.lean"
)
SOURCE_MAP_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_StressEnergyExpectationSourceMap.lean"
)
RESIDUAL_ONLY_OBSTRUCTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_StressEnergySourceMapResidualOnlyObstruction.lean"
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

CONSUMED_TARGET = "prepare_qft_gr_source_map_semantics_retained_blocker_protocol_row"
READINESS_REVIEW_TARGET = "review_qft_gr_source_map_semantics_protocol_row_readiness"
SURFACE_ID = "qft_gr_source_map_semantics_retained_blocker_protocol_row_v0"
RETAINED_BLOCKER = "PHASE1-BLOCKER-QFTGR-STRESS-ENERGY-EXPECTATION-SOURCE-MAP-RETAINED"
AUTHORITY_ROW = "ROW-SEAM-QFT-GR-001"
SEAM_ID = "SEAM-QFT-GR"
PROTOCOL_EVIDENCE = str(PROTOCOL_ROW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
POST_QMSTAT_REVIEW_EVIDENCE = str(
    POST_QMSTAT_PRIORITIZATION_REVIEW_PATH.relative_to(REPO_ROOT)
).replace("\\", "/")


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _registry() -> dict[str, Any]:
    return json.loads(_read(REGISTRY_PATH))


def _workstream(payload: dict[str, Any], workstream_id: str) -> dict[str, Any]:
    for workstream in payload["workstreams"]:
        if workstream["workstream_id"] == workstream_id:
            return workstream
    raise AssertionError(f"Missing workstream: {workstream_id}")


def test_protocol_row_records_qft_gr_blocker_and_obligations() -> None:
    text = _read(PROTOCOL_ROW_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        READINESS_REVIEW_TARGET,
        AUTHORITY_ROW,
        SEAM_ID,
        "phase1BlockerQFTGRStressEnergyExpectationSourceMapRetainedId",
        "QFT_GR_STRESS_ENERGY_EXPECTATION_SOURCE_MAP_v0",
        "QFT_GR_SOURCE_MAP_RESIDUAL_ONLY_SEMANTIC_OBSTRUCTION_FRESH_DELTA_v0",
        "QFT_GR_STRESS_ENERGY_OPERATOR_DOMAIN_DERIVATION_OBLIGATION_v0",
        "QFT_GR_QFT_STATE_EXPECTATION_FUNCTIONAL_DERIVATION_OBLIGATION_v0",
        "QFT_GR_RENORMALIZED_EXPECTATION_DERIVATION_OBLIGATION_v0",
        "QFT_GR_WEAK_CURVATURE_SOURCE_IDENTIFICATION_DERIVATION_OBLIGATION_v0",
        "QFT_GR_COVARIANCE_CONSERVATION_DERIVATION_OBLIGATION_v0",
        "qft_gr_source_map_semantics_protocol_row_required_evidence_v0",
        "qft_gr_source_map_semantics_protocol_row_minimum_readiness_v0",
        "qft_gr_source_map_semantics_protocol_row_frontier_target_v0",
    }:
        assert token in text

    source_map_text = _read(SOURCE_MAP_PATH)
    obstruction_text = _read(RESIDUAL_ONLY_OBSTRUCTION_PATH)
    assert "phase1BlockerQFTGRStressEnergyExpectationSourceMapRetainedId" in source_map_text
    assert "QFTGRFullSourceMapSemanticRequirements" in obstruction_text
    assert "residual_only_zero_evidence_does_not_close_full_source_map_semantics_v0" in (
        obstruction_text
    )


def test_protocol_row_preserves_fail_closed_boundaries() -> None:
    text = _read(PROTOCOL_ROW_PATH)

    for theorem in {
        "qft_gr_source_map_semantics_protocol_row_physics_incomplete_v0",
        "qft_gr_source_map_semantics_protocol_row_no_theorem_work_v0",
        "qft_gr_source_map_semantics_protocol_row_no_lane_reopen_v0",
        "qft_gr_source_map_semantics_protocol_row_no_same_lane_theorem_continuation_v0",
        "qft_gr_source_map_semantics_protocol_row_no_seam_closure_v0",
        "qft_gr_source_map_semantics_protocol_row_no_semiclassical_gravity_claim_v0",
        "qft_gr_source_map_semantics_protocol_row_no_einstein_equation_claim_v0",
        "qft_gr_source_map_semantics_protocol_row_phase2_not_authorized_v0",
        "qft_gr_source_map_semantics_protocol_row_master_action_not_promoted_v0",
        "qft_gr_source_map_semantics_protocol_row_no_empirical_claim_v0",
        "qft_gr_source_map_semantics_protocol_row_governance_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_frontier_and_aggregate_rotate_to_readiness_review() -> None:
    assert_frontier_matches_registry()
    aggregate_text = _read(AGGREGATE_PATH)
    frontier_text = _read(FRONTIER_PATH)
    post_qmstat_text = _read(POST_QMSTAT_PRIORITIZATION_REVIEW_PATH)

    assert (
        "import ToeFormal.Derivation.QFTGRSourceMapSemanticsRetainedBlockerProtocolRow"
        in aggregate_text
    )
    assert f'def previousLiveNextStrictTargetV0 : String :=\n  "{CONSUMED_TARGET}"' in frontier_text
    assert f'def currentLiveNextStrictTargetV0 : String :=\n  "{READINESS_REVIEW_TARGET}"' in (
        frontier_text
    )
    assert f'next_strict_slice :=\n        "{READINESS_REVIEW_TARGET}"' in frontier_text
    assert f'  "{CONSUMED_TARGET}"' in post_qmstat_text


def test_loop_registry_tracks_protocol_row_as_current_surface() -> None:
    assert_current_target_consistent()
    assert_forbidden_promotions_closed()
    payload = _registry()
    state = payload["current_target_state"]

    assert state["previous_live_next_target"] == CONSUMED_TARGET
    assert state["live_next_target"] == READINESS_REVIEW_TARGET
    assert state["live_next_target_evidence"] == PROTOCOL_EVIDENCE
    assert state["active_lane"] == "master_action_dependency_frontier"
    assert READINESS_REVIEW_TARGET in payload["next_strict_target_coverage"]

    qft_gr = _workstream(payload, "qft_gr_source_map")
    assert qft_gr["status"] == "paused"
    assert qft_gr["protocol_row_preparation_target"] == CONSUMED_TARGET
    assert qft_gr["protocol_row_preparation_status"] == "completed_protocol_row_prepared"
    assert qft_gr["protocol_row_status"] == "prepared_from_post_qm_stat_prioritization"
    assert qft_gr["protocol_row_evidence"] == PROTOCOL_EVIDENCE
    assert qft_gr["protocol_row_next_review"] == READINESS_REVIEW_TARGET
    assert qft_gr["source_map_semantics_primary_blocker"] == "full_source_map_semantic_closure"
    assert qft_gr["stress_energy_operator_domain_obligation"] == "still_required"
    assert qft_gr["qft_state_expectation_functional_obligation"] == "still_required"
    assert qft_gr["renormalized_expectation_obligation"] == "still_required"
    assert qft_gr["gr_weak_curvature_source_identification_obligation"] == "still_required"
    assert qft_gr["covariance_conservation_obligation"] == "still_required"
    assert qft_gr["readiness_review_status"] == "pending"
    assert qft_gr["theorem_work_authorized"] == (
        "no_protocol_row_prepared_readiness_review_pending"
    )

    master_action = _workstream(payload, "master_action_dependency_frontier")
    assert master_action["latest_surface"] == SURFACE_ID
    assert master_action["consumed_target"] == CONSUMED_TARGET
    assert master_action["authorization_evidence"] == PROTOCOL_EVIDENCE
    assert master_action["authorized_next_strict_target"] == READINESS_REVIEW_TARGET
    assert master_action["qft_gr_protocol_row_authority_row"] == AUTHORITY_ROW
    assert master_action["qft_gr_protocol_row_seam"] == SEAM_ID
    assert master_action["qft_gr_protocol_row_retained_blocker"] == RETAINED_BLOCKER
    assert master_action["qft_gr_protocol_row_next_review"] == READINESS_REVIEW_TARGET
    assert master_action["qft_gr_protocol_row_evidence"] == PROTOCOL_EVIDENCE

    edges = {(edge["from"], edge["to"]) for edge in payload["dependency_edges"]}
    assert (
        "qm_stat_retained_blocker_prioritization_after_source_probability_result",
        "qft_gr_source_map_semantics_retained_blocker_protocol_row",
    ) in edges
    assert (
        "qft_gr_source_map_semantics_retained_blocker_protocol_row",
        "qft_gr_source_map_semantics_protocol_row_readiness_review",
    ) in edges


def test_public_surfaces_expose_protocol_row_and_manifest_remains_unchanged() -> None:
    assert_public_surfaces_match_registry()
    for path in [README_PATH, STATE_PATH, ROADMAP_PATH, STRICT_MAP_PATH]:
        text = _read(path)
        assert "QFTGRSourceMapSemanticsRetainedBlockerProtocolRow.lean" in text
        assert READINESS_REVIEW_TARGET in text
        assert RETAINED_BLOCKER in text

    for path in [STATE_PATH, STRICT_MAP_PATH, SEAM_REGISTRY_PATH, SEAM_INVENTORY_PATH]:
        text = _read(path)
        assert "QFT_GR_SOURCE_MAP_SEMANTICS_PROTOCOL_ROW" in text
        assert PROTOCOL_EVIDENCE in text

    inventory_text = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-QFTGR-SOURCE-MAP-SEMANTICS-PROTOCOL-ROW-v0" in inventory_text
    assert PROTOCOL_EVIDENCE in inventory_text
    assert POST_QMSTAT_REVIEW_EVIDENCE in inventory_text
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_source_map_semantics_protocol_row_gate.py"
    )
