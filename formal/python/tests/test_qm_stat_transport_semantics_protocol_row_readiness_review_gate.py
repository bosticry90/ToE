from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
READINESS_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMSTATTransportSemanticsProtocolRowReadinessReview.lean"
)
PROTOCOL_ROW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMSTATTransportSemanticsRetainedBlockerProtocolRow.lean"
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

READINESS_REVIEW_TARGET = "review_qm_stat_transport_semantics_protocol_row_readiness"
LIVE_TARGET = "derive_or_refute_qm_stat_source_probability_extraction_semantics"
SURFACE_ID = "qm_stat_transport_semantics_protocol_row_readiness_review_v0"
PROTOCOL_SURFACE_ID = "qm_stat_transport_semantics_retained_blocker_protocol_row_v0"
RETAINED_BLOCKER = "PHASE1-BLOCKER-QMSTAT-TRANSPORT-RESIDUAL-PACKAGE-RETAINED"
READINESS_EVIDENCE = str(READINESS_REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")


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


def test_readiness_review_records_bounded_source_probability_authorization() -> None:
    text = _read(READINESS_REVIEW_PATH)

    for token in {
        SURFACE_ID,
        READINESS_REVIEW_TARGET,
        LIVE_TARGET,
        "authorize_bounded_source_probability_extraction",
        "authorizeBoundedSourceProbabilityExtraction",
        ".sourceProbabilityExtraction",
        "qm_stat_transport_semantics_readiness_review_authorizes_source_probability_v0",
        "qm_stat_transport_semantics_readiness_review_selected_next_target_v0",
        "qm_stat_transport_semantics_readiness_review_frontier_target_v0",
    }:
        assert token in text

    protocol_text = _read(PROTOCOL_ROW_PATH)
    assert PROTOCOL_SURFACE_ID in protocol_text
    assert "qmStatTransportSemanticsReadinessReviewTargetId" in protocol_text


def test_readiness_review_preserves_fail_closed_boundaries() -> None:
    text = _read(READINESS_REVIEW_PATH)

    for theorem in {
        "qm_stat_transport_semantics_readiness_review_no_broader_theorem_work_v0",
        "qm_stat_transport_semantics_readiness_review_target_entropy_not_authorized_v0",
        "qm_stat_transport_semantics_readiness_review_transport_map_not_authorized_v0",
        "qm_stat_transport_semantics_readiness_review_coarse_graining_not_authorized_v0",
        "qm_stat_transport_semantics_readiness_review_residual_closure_not_authorized_v0",
        "qm_stat_transport_semantics_readiness_review_no_seam_closure_v0",
        "qm_stat_transport_semantics_readiness_review_no_stat_mechanics_claim_v0",
        "qm_stat_transport_semantics_readiness_review_phase2_not_authorized_v0",
        "qm_stat_transport_semantics_readiness_review_master_action_not_promoted_v0",
        "qm_stat_transport_semantics_readiness_review_no_empirical_claim_v0",
        "qm_stat_transport_semantics_readiness_review_governance_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_frontier_and_aggregate_point_to_source_probability_target() -> None:
    aggregate_text = _read(AGGREGATE_PATH)
    frontier_text = _read(FRONTIER_PATH)

    assert "import ToeFormal.Derivation.QMSTATTransportSemanticsProtocolRowReadinessReview" in aggregate_text
    assert f'def previousLiveNextStrictTargetV0 : String :=\n  "{READINESS_REVIEW_TARGET}"' in frontier_text
    assert f'def currentLiveNextStrictTargetV0 : String :=\n  "{LIVE_TARGET}"' in frontier_text
    assert f'next_strict_slice := "{LIVE_TARGET}"' in frontier_text
    assert "QM-STAT transport semantics protocol-row readiness review" in frontier_text


def test_loop_registry_rotates_active_lane_to_qm_stat_bounded_slice() -> None:
    payload = _registry()
    state = payload["current_target_state"]

    assert state["previous_live_next_target"] == READINESS_REVIEW_TARGET
    assert state["live_next_target"] == LIVE_TARGET
    assert state["live_next_target_evidence"] == READINESS_EVIDENCE
    assert state["active_lane"] == "qm_stat_transport_residual"
    assert "qm_stat_transport_residual" not in state["paused_lanes"]
    assert "master_action_dependency_frontier" in state["paused_lanes"]
    assert LIVE_TARGET in payload["next_strict_target_coverage"]

    active = [item for item in payload["workstreams"] if item.get("status") == "active"]
    assert [item["workstream_id"] for item in active] == ["qm_stat_transport_residual"]
    qm_stat = active[0]
    assert qm_stat["authorization_evidence"] == READINESS_EVIDENCE
    assert qm_stat["consumed_target"] == READINESS_REVIEW_TARGET
    assert qm_stat["prior_surface"] == PROTOCOL_SURFACE_ID
    assert qm_stat["latest_surface"] == SURFACE_ID
    assert qm_stat["authorized_next_strict_target"] == LIVE_TARGET
    assert qm_stat["bounded_source_probability_slice_authorized"] == "yes"
    assert qm_stat["theorem_work_authorized"] == "bounded_source_probability_extraction_only"
    assert qm_stat["source_probability_extraction_obligation"] == "authorized_next_slice"
    assert qm_stat["target_entropy_semantics_authorized"] == "no"
    assert qm_stat["transport_map_semantics_authorized"] == "no"
    assert qm_stat["coarse_graining_irreversibility_authorized"] == "no"
    assert qm_stat["residual_package_semantic_closure_authorized"] == "no"

    master_action = _workstream(payload, "master_action_dependency_frontier")
    assert master_action["status"] == "paused"
    assert master_action["readiness_review_status"] == "completed"
    assert master_action["authorized_next_strict_target"] == LIVE_TARGET
    assert master_action["promotion_authorized"] == "no"

    edges = {(edge["from"], edge["to"]) for edge in payload["dependency_edges"]}
    assert (
        "qm_stat_transport_semantics_retained_blocker_protocol_row",
        "qm_stat_transport_semantics_protocol_row_readiness_review",
    ) in edges
    assert (
        "qm_stat_transport_semantics_protocol_row_readiness_review",
        "qm_stat_source_probability_extraction_semantics",
    ) in edges


def test_public_surfaces_and_manifest_boundary_are_synchronized() -> None:
    for path in [README_PATH, STATE_PATH, ROADMAP_PATH, STRICT_MAP_PATH]:
        text = _read(path)
        assert LIVE_TARGET in text, f"{path} missing live target"
        assert "QMSTATTransportSemanticsProtocolRowReadinessReview.lean" in text

    for path in [SEAM_REGISTRY_PATH, SEAM_INVENTORY_PATH]:
        text = _read(path)
        assert "QM_STAT_TRANSPORT_SEMANTICS_READINESS_REVIEW" in text
        assert LIVE_TARGET in text

    inventory_text = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-QMSTAT-TRANSPORT-SEMANTICS-READINESS-REVIEW-v0" in inventory_text
    assert READINESS_EVIDENCE in inventory_text
    assert "test_qm_stat_transport_semantics_protocol_row_readiness_review_gate.py" not in _read(
        GOVERNANCE_MANIFEST_PATH
    )
