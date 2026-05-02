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
    / "MasterActionDependencyGraphReview.lean"
)
PRIORITIZATION_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionRetainedBlockerPrioritizationReview.lean"
)
PROTOCOL_ROW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMSTATTransportSemanticsRetainedBlockerProtocolRow.lean"
)
AUDIT_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionCitationLanguageAudit.lean"
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

CONSUMED_TARGET = "review_master_action_dependency_graph_after_citation_language_audit"
PRIORITIZATION_TARGET = "prioritize_retained_blockers_after_master_action_dependency_graph_review"
PROTOCOL_TARGET = "prepare_qm_stat_transport_semantics_retained_blocker_protocol_row"
READINESS_REVIEW_TARGET = "review_qm_stat_transport_semantics_protocol_row_readiness"
LIVE_TARGET = "derive_or_refute_qm_stat_source_probability_extraction_semantics"
READINESS_EVIDENCE = "formal/toe_formal/ToeFormal/Derivation/QMSTATTransportSemanticsProtocolRowReadinessReview.lean"
SURFACE_ID = "master_action_dependency_graph_review_v0"
REVIEW_EVIDENCE = str(REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
PRIORITIZATION_EVIDENCE = str(PRIORITIZATION_REVIEW_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
PROTOCOL_EVIDENCE = str(PROTOCOL_ROW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _registry() -> dict[str, Any]:
    return json.loads(_read(REGISTRY_PATH))


def test_master_action_dependency_graph_review_records_negative_decision() -> None:
    text = _read(REVIEW_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        PRIORITIZATION_TARGET,
        LIVE_TARGET,
        "master_action_dependency_graph_review_consumes_live_target_v0",
        "master_action_dependency_graph_review_selected_next_target_v0",
        "master_action_dependency_graph_review_frontier_target_v0",
        "master_action_dependency_graph_review_preserves_dependency_kind_ids_v0",
        "master_action_dependency_graph_review_preserves_retained_ids_v0",
        "master_action_dependency_graph_review_boundary_count_v0",
        "master_action_dependency_graph_review_completed_v0",
        "master_action_dependency_graph_review_graph_unchanged_v0",
        "master_action_dependency_graph_review_classes_unchanged_v0",
        "master_action_dependency_graph_review_no_lane_unblocked_v0",
        "master_action_dependency_graph_review_no_promotion_authorized_v0",
    }:
        assert token in text


def test_review_preserves_lane_and_nonpromotion_boundaries() -> None:
    text = _read(REVIEW_PATH)

    for token in {
        "master_action_dependency_graph_review_scalar_lane_not_unblocked_v0",
        "master_action_dependency_graph_review_qm_stat_lane_not_unblocked_v0",
        "master_action_dependency_graph_review_qft_gr_lane_not_unblocked_v0",
        "master_action_dependency_graph_review_sr_cosmo_lane_not_unblocked_v0",
        "master_action_dependency_graph_review_em_qft_lane_not_unblocked_v0",
        "master_action_dependency_graph_review_no_seam_closure_v0",
        "master_action_dependency_graph_review_phase2_not_authorized_v0",
        "master_action_dependency_graph_review_master_action_not_promoted_v0",
        "master_action_dependency_graph_review_no_empirical_claim_v0",
        "master_action_dependency_graph_review_governance_manifest_not_enrolled_v0",
    }:
        assert token in text


def test_frontier_and_aggregate_rotate_to_retained_blocker_prioritization() -> None:
    aggregate_text = _read(AGGREGATE_PATH)
    frontier_text = _read(FRONTIER_PATH)
    audit_text = _read(AUDIT_PATH)

    assert "import ToeFormal.Derivation.MasterActionDependencyGraphReview" in aggregate_text
    assert (
        "import ToeFormal.Derivation.MasterActionRetainedBlockerPrioritizationReview"
        in aggregate_text
    )
    assert (
        "import ToeFormal.Derivation.QMSTATTransportSemanticsRetainedBlockerProtocolRow"
        in aggregate_text
    )
    assert f'def previousLiveNextStrictTargetV0 : String :=\n  "{READINESS_REVIEW_TARGET}"' in frontier_text
    assert f'def currentLiveNextStrictTargetV0 : String :=\n  "{LIVE_TARGET}"' in frontier_text
    assert f'next_strict_slice :=\n        "{LIVE_TARGET}"' in frontier_text
    assert "QM-STAT transport semantics protocol-row readiness review" in frontier_text
    assert "master_action_citation_language_audit_frontier_target_v0" in audit_text


def test_loop_registry_tracks_dependency_graph_review_as_current_surface() -> None:
    payload = _registry()
    state = payload["current_target_state"]

    assert state["previous_live_next_target"] == READINESS_REVIEW_TARGET
    assert state["live_next_target"] == LIVE_TARGET
    assert state["live_next_target_evidence"] == READINESS_EVIDENCE
    assert state["active_lane"] == "qm_stat_transport_residual"
    assert LIVE_TARGET in payload["next_strict_target_coverage"]

    active = [item for item in payload["workstreams"] if item.get("status") == "active"]
    assert [item["workstream_id"] for item in active] == ["qm_stat_transport_residual"]
    workstream = active[0]
    assert workstream["authorization_evidence"] == READINESS_EVIDENCE
    assert workstream["consumed_target"] == READINESS_REVIEW_TARGET
    assert workstream["prior_surface"] == "qm_stat_transport_semantics_retained_blocker_protocol_row_v0"
    assert workstream["latest_surface"] == "qm_stat_transport_semantics_protocol_row_readiness_review_v0"
    assert workstream["authorized_next_strict_target"] == LIVE_TARGET
    assert workstream["same_lane_continuation"] == "authorized_bounded_source_probability_extraction_slice"

    edges = {(edge["from"], edge["to"]) for edge in payload["dependency_edges"]}
    assert (
        "master_action_citation_language_audit",
        "master_action_dependency_graph_review",
    ) in edges
    assert (
        "master_action_dependency_graph_review",
        "master_action_retained_blocker_prioritization_review",
    ) in edges
    assert (
        "master_action_retained_blocker_prioritization_review",
        "qm_stat_transport_semantics_retained_blocker_protocol_row",
    ) in edges


def test_public_surfaces_expose_review_and_manifest_remains_unchanged() -> None:
    for path in [README_PATH, STATE_PATH, ROADMAP_PATH, STRICT_MAP_PATH]:
        text = _read(path)
        assert LIVE_TARGET in text, f"{path} missing live target"

    for path in [STATE_PATH, STRICT_MAP_PATH, SEAM_REGISTRY_PATH, SEAM_INVENTORY_PATH]:
        assert "MasterActionDependencyGraphReview.lean" in _read(path)
        assert "MasterActionRetainedBlockerPrioritizationReview.lean" in _read(path)
        assert "QMSTATTransportSemanticsRetainedBlockerProtocolRow.lean" in _read(path)

    inventory_text = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-MASTER-ACTION-DEPENDENCY-GRAPH-REVIEW-v0" in inventory_text
    assert "INV-MATH-MASTER-ACTION-RETAINED-BLOCKER-PRIORITIZATION-REVIEW-v0" in inventory_text
    assert "INV-MATH-QMSTAT-TRANSPORT-SEMANTICS-PROTOCOL-ROW-v0" in inventory_text
    assert REVIEW_EVIDENCE in inventory_text
    assert PRIORITIZATION_EVIDENCE in inventory_text
    assert PROTOCOL_EVIDENCE in inventory_text
    assert "test_master_action_dependency_graph_review_gate.py" not in _read(
        GOVERNANCE_MANIFEST_PATH
    )
