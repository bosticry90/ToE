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
PROTOCOL_ROW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMSTATTransportSemanticsRetainedBlockerProtocolRow.lean"
)
PRIORITIZATION_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionRetainedBlockerPrioritizationReview.lean"
)
RESIDUAL_PACKAGE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QM_STAT_TransportResidualPackage.lean"
)
AGGREGATE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
READINESS_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMSTATTransportSemanticsProtocolRowReadinessReview.lean"
)
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

CONSUMED_TARGET = "prepare_qm_stat_transport_semantics_retained_blocker_protocol_row"
READINESS_REVIEW_TARGET = "review_qm_stat_transport_semantics_protocol_row_readiness"
SOURCE_PROBABILITY_TARGET = current_target_state()["previous_live_next_target"]
LIVE_TARGET = current_target_state()["live_next_target"]
SURFACE_ID = "qm_stat_transport_semantics_retained_blocker_protocol_row_v0"
READINESS_SURFACE_ID = "qm_stat_transport_semantics_protocol_row_readiness_review_v0"
SOURCE_PROBABILITY_SURFACE_ID = "QM_STAT_SOURCE_PROBABILITY_EXTRACTION_SEMANTICS_v0"
RETAINED_BLOCKER = "PHASE1-BLOCKER-QMSTAT-TRANSPORT-RESIDUAL-PACKAGE-RETAINED"
AUTHORITY_ROW = "ROW-SEAM-QM-STAT-001"
SEAM_ID = "SEAM-QM-STAT"
PROTOCOL_EVIDENCE = str(PROTOCOL_ROW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
SOURCE_PROBABILITY_EVIDENCE = current_target_state()["live_next_target_evidence"]


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


def test_protocol_row_records_qm_stat_blocker_and_obligations() -> None:
    text = _read(PROTOCOL_ROW_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        READINESS_REVIEW_TARGET,
        AUTHORITY_ROW,
        SEAM_ID,
        "phase1BlockerQMSTATTransportResidualPackageRetainedId",
        "QM_STAT_UNIFIED_TRANSPORT_RESIDUAL_PACKAGE_v0",
        "QM_STAT_TRANSPORT_RESIDUAL_COMPONENT_EVIDENCE_FRESH_DELTA_v0",
        "QM_STAT_SOURCE_QM_EVOLUTION_PROBABILITY_EXTRACTION_OBLIGATION_v0",
        "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_OBLIGATION_v0",
        "QM_STAT_TRANSPORT_MAP_SEMANTIC_DERIVATION_OBLIGATION_v0",
        "QM_STAT_COARSE_GRAINING_IRREVERSIBILITY_OBLIGATION_v0",
        "qm_stat_transport_semantics_protocol_row_required_evidence_v0",
        "qm_stat_transport_semantics_protocol_row_minimum_readiness_v0",
        "qm_stat_transport_semantics_protocol_row_frontier_target_v0",
    }:
        assert token in text

    residual_text = _read(RESIDUAL_PACKAGE_PATH)
    assert "phase1BlockerQMSTATTransportResidualPackageRetainedId" in residual_text
    assert "qmStatTransportResidualComponentEvidenceFreshDeltaId" in residual_text


def test_protocol_row_preserves_fail_closed_boundaries() -> None:
    text = _read(PROTOCOL_ROW_PATH)

    for theorem in {
        "qm_stat_transport_semantics_protocol_row_physics_incomplete_v0",
        "qm_stat_transport_semantics_protocol_row_no_theorem_work_v0",
        "qm_stat_transport_semantics_protocol_row_no_lane_reopen_v0",
        "qm_stat_transport_semantics_protocol_row_no_same_lane_theorem_continuation_v0",
        "qm_stat_transport_semantics_protocol_row_no_seam_closure_v0",
        "qm_stat_transport_semantics_protocol_row_phase2_not_authorized_v0",
        "qm_stat_transport_semantics_protocol_row_master_action_not_promoted_v0",
        "qm_stat_transport_semantics_protocol_row_no_empirical_claim_v0",
        "qm_stat_transport_semantics_protocol_row_governance_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_frontier_and_aggregate_rotate_past_readiness_review() -> None:
    assert_frontier_matches_registry()
    aggregate_text = _read(AGGREGATE_PATH)
    frontier_text = _read(FRONTIER_PATH)
    prioritization_text = _read(PRIORITIZATION_REVIEW_PATH)

    assert (
        "import ToeFormal.Derivation.QMSTATTransportSemanticsRetainedBlockerProtocolRow"
        in aggregate_text
    )
    assert "import ToeFormal.Derivation.QMSTATTransportSemanticsProtocolRowReadinessReview" in aggregate_text
    assert "source-probability extraction supplied route and contract-only obstruction" in frontier_text
    assert f'  "{CONSUMED_TARGET}"' in prioritization_text


def test_loop_registry_tracks_protocol_row_as_current_surface() -> None:
    assert_current_target_consistent()
    payload = _registry()

    assert LIVE_TARGET in payload["next_strict_target_coverage"]

    qm_stat = _workstream(payload, "qm_stat_transport_residual")
    assert qm_stat["protocol_row_status"] == "prepared_from_master_action_prioritization"
    assert qm_stat["protocol_row_evidence"] == PROTOCOL_EVIDENCE
    assert qm_stat["protocol_row_next_review"] == READINESS_REVIEW_TARGET
    assert qm_stat["theorem_work_authorized"] == "no_pending_source_probability_result_review"
    assert (
        qm_stat["source_probability_extraction_obligation"]
        == "retained_as_supplied_semantics_not_contract_derived"
    )
    assert qm_stat["target_stat_entropy_semantics_obligation"] == "still_required"
    assert qm_stat["transport_semantic_map_obligation"] == "still_required"
    assert qm_stat["coarse_graining_irreversibility_obligation"] == "still_required"
    assert qm_stat["target_entropy_semantics_authorized"] == "no"
    assert qm_stat["transport_map_semantics_authorized"] == "no"
    assert qm_stat["coarse_graining_irreversibility_authorized"] == "no"
    assert qm_stat["residual_package_semantic_closure_authorized"] == "no"

    edges = {(edge["from"], edge["to"]) for edge in payload["dependency_edges"]}
    assert (
        "master_action_retained_blocker_prioritization_review",
        "qm_stat_transport_semantics_retained_blocker_protocol_row",
    ) in edges
    assert (
        "qm_stat_transport_semantics_retained_blocker_protocol_row",
        "qm_stat_transport_semantics_protocol_row_readiness_review",
    ) in edges
    assert (
        "qm_stat_source_probability_extraction_semantics",
        "qm_stat_source_probability_extraction_semantics_result_review",
    ) in edges


def test_public_surfaces_expose_protocol_row_and_manifest_remains_unchanged() -> None:
    assert_public_surfaces_match_registry()
    for path in [README_PATH, STATE_PATH, ROADMAP_PATH, STRICT_MAP_PATH]:
        text = _read(path)
        assert "QMSTATTransportSemanticsRetainedBlockerProtocolRow.lean" in text
        assert "QMSTATTransportSemanticsProtocolRowReadinessReview.lean" in text
        assert "QM_STAT_SourceProbabilityExtractionSemantics.lean" in text

    for path in [STATE_PATH, STRICT_MAP_PATH, SEAM_REGISTRY_PATH, SEAM_INVENTORY_PATH]:
        text = _read(path)
        assert "QM_STAT_TRANSPORT_SEMANTICS_PROTOCOL_ROW" in text
        assert (
            PROTOCOL_EVIDENCE in text
            or "QMSTATTransportSemanticsRetainedBlockerProtocolRow.lean" in text
        )

    inventory_text = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-QMSTAT-TRANSPORT-SEMANTICS-PROTOCOL-ROW-v0" in inventory_text
    assert PROTOCOL_EVIDENCE in inventory_text
    assert_focused_gate_not_manifest_enrolled("test_qm_stat_transport_semantics_protocol_row_gate.py")
