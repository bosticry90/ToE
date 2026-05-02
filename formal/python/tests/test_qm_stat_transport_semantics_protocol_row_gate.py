from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


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
LIVE_TARGET = "review_qm_stat_transport_semantics_protocol_row_readiness"
SURFACE_ID = "qm_stat_transport_semantics_retained_blocker_protocol_row_v0"
RETAINED_BLOCKER = "PHASE1-BLOCKER-QMSTAT-TRANSPORT-RESIDUAL-PACKAGE-RETAINED"
AUTHORITY_ROW = "ROW-SEAM-QM-STAT-001"
SEAM_ID = "SEAM-QM-STAT"
PROTOCOL_EVIDENCE = str(PROTOCOL_ROW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")


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
        LIVE_TARGET,
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


def test_frontier_and_aggregate_rotate_to_readiness_review() -> None:
    aggregate_text = _read(AGGREGATE_PATH)
    frontier_text = _read(FRONTIER_PATH)
    prioritization_text = _read(PRIORITIZATION_REVIEW_PATH)

    assert (
        "import ToeFormal.Derivation.QMSTATTransportSemanticsRetainedBlockerProtocolRow"
        in aggregate_text
    )
    assert f'def previousLiveNextStrictTargetV0 : String :=\n  "{CONSUMED_TARGET}"' in frontier_text
    assert f'def currentLiveNextStrictTargetV0 : String :=\n  "{LIVE_TARGET}"' in frontier_text
    assert f'next_strict_slice := "review_qm_stat_transport_semantics_protocol_row_readiness"' in frontier_text
    assert "QM-STAT transport semantics retained-blocker protocol row" in frontier_text
    assert f'  "{CONSUMED_TARGET}"' in prioritization_text


def test_loop_registry_tracks_protocol_row_as_current_surface() -> None:
    payload = _registry()
    state = payload["current_target_state"]

    assert state["previous_live_next_target"] == CONSUMED_TARGET
    assert state["live_next_target"] == LIVE_TARGET
    assert state["live_next_target_evidence"] == PROTOCOL_EVIDENCE
    assert state["active_lane"] == "master_action_dependency_frontier"
    assert LIVE_TARGET in payload["next_strict_target_coverage"]

    active = [item for item in payload["workstreams"] if item.get("status") == "active"]
    assert [item["workstream_id"] for item in active] == ["master_action_dependency_frontier"]
    workstream = active[0]
    assert workstream["authorization_evidence"] == PROTOCOL_EVIDENCE
    assert workstream["consumed_target"] == CONSUMED_TARGET
    assert workstream["prior_consumed_target"] == (
        "prioritize_retained_blockers_after_master_action_dependency_graph_review"
    )
    assert workstream["prior_surface"] == "master_action_retained_blocker_prioritization_review_v0"
    assert workstream["latest_surface"] == SURFACE_ID
    assert workstream["qm_stat_transport_semantics_protocol_row_status"] == "prepared"
    assert workstream["protocol_row_authority_row"] == AUTHORITY_ROW
    assert workstream["protocol_row_seam"] == SEAM_ID
    assert workstream["protocol_row_retained_blocker"] == RETAINED_BLOCKER
    assert workstream["protocol_row_next_review"] == LIVE_TARGET
    assert workstream["next_action_scope"] == "protocol_readiness_review_only_no_theorem_work"
    assert workstream["theorem_work_authorized"] == "no"
    assert workstream["lane_unblocked"] == "no"
    assert workstream["dependency_classes_changed"] == "no"
    assert workstream["promotion_authorized"] == "no"
    assert workstream["authorized_next_strict_target"] == LIVE_TARGET
    assert workstream["same_lane_continuation"] == "protocol_readiness_review_only"

    qm_stat = _workstream(payload, "qm_stat_transport_residual")
    assert qm_stat["status"] == "paused"
    assert qm_stat["same_lane_continuation"] == "not_authorized"
    assert qm_stat["protocol_row_status"] == "prepared_from_master_action_prioritization"
    assert qm_stat["protocol_row_evidence"] == PROTOCOL_EVIDENCE
    assert qm_stat["protocol_row_next_review"] == LIVE_TARGET
    assert qm_stat["theorem_work_authorized"] == "no"
    assert qm_stat["source_probability_extraction_obligation"] == "still_required"
    assert qm_stat["target_stat_entropy_semantics_obligation"] == "still_required"
    assert qm_stat["transport_semantic_map_obligation"] == "still_required"
    assert qm_stat["coarse_graining_irreversibility_obligation"] == "still_required"

    edges = {(edge["from"], edge["to"]) for edge in payload["dependency_edges"]}
    assert (
        "master_action_retained_blocker_prioritization_review",
        "qm_stat_transport_semantics_retained_blocker_protocol_row",
    ) in edges


def test_public_surfaces_expose_protocol_row_and_manifest_remains_unchanged() -> None:
    for path in [README_PATH, STATE_PATH, ROADMAP_PATH, STRICT_MAP_PATH]:
        text = _read(path)
        assert LIVE_TARGET in text, f"{path} missing live target"
        assert "QMSTATTransportSemanticsRetainedBlockerProtocolRow.lean" in text

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
    assert "test_qm_stat_transport_semantics_protocol_row_gate.py" not in _read(
        GOVERNANCE_MANIFEST_PATH
    )
