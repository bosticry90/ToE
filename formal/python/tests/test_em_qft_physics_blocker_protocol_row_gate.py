from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_current_target_consistent,
    assert_focused_gate_not_manifest_enrolled,
    assert_frontier_matches_registry,
    assert_public_surfaces_match_registry,
    current_target_state,
)


REPO_ROOT = find_repo_root(Path(__file__))
PROTOCOL_ROW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "EMQFTPhysicsBlockerProtocolRow.lean"
)
CROSS_PILLAR_FRONTIER_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CrossPillarClosureFrontier.lean"
)
DERIVATION_DIR = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation"
SHARED_DYNAMICS_BRIDGE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "EM_QFT_SharedDynamicsResidualUnificationBridge.lean"
)
INTERFACE_ALIGNMENT_BRIDGE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "EM_QFT_InterfaceAlignmentSemanticBridge.lean"
)
POST_BUDGET_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "EMQFTPostBudgetCrossPillarReview.lean"
)
MASTER_ACTION_CITATION_USAGE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionRetainedAssumptionCitationUsage.lean"
)
MASTER_ACTION_CITATION_AUDIT_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionCitationLanguageAudit.lean"
)
MASTER_ACTION_DEPENDENCY_GRAPH_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionDependencyGraphReview.lean"
)
MASTER_ACTION_RETAINED_BLOCKER_PRIORITIZATION_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionRetainedBlockerPrioritizationReview.lean"
)
QM_STAT_PROTOCOL_ROW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMSTATTransportSemanticsRetainedBlockerProtocolRow.lean"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
GOVERNANCE_MANIFEST_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_TEST_MANIFEST_v1.json"
)
SEAM_REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md"
)
SEAM_INVENTORY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md"
)

CONSUMED_TARGET = "extract_em_qft_physics_blocker_into_protocol_row"
PROTOCOL_SUCCESSOR_TARGET = "derive_or_refute_em_qft_shared_dynamics_residual_unification_bridge"
INTERFACE_TARGET = "derive_or_refute_em_qft_interface_alignment_semantic_bridge"
POST_BUDGET_TARGET = "em_qft_post_budget_cross_pillar_review"
CITATION_USAGE_TARGET = "cite_only_bounded_retained_assumptions"
AUDIT_TARGET = "audit_master_action_citation_language_against_retained_boundaries"
REVIEW_TARGET = "review_master_action_dependency_graph_after_citation_language_audit"
PRIORITIZATION_TARGET = "prioritize_retained_blockers_after_master_action_dependency_graph_review"
PROTOCOL_TARGET = "prepare_qm_stat_transport_semantics_retained_blocker_protocol_row"
READINESS_REVIEW_TARGET = "review_qm_stat_transport_semantics_protocol_row_readiness"
SOURCE_PROBABILITY_TARGET = current_target_state()["previous_live_next_target"]
LIVE_TARGET = current_target_state()["live_next_target"]
READINESS_EVIDENCE = current_target_state()["live_next_target_evidence"]
PRIMARY_BLOCKER = "shared_dynamics_and_residual_unification"
SECONDARY_BLOCKER = "interface_alignment_semantic_bridge"
REQUIRED_EVIDENCE = {
    "EM_QFT_INTERFACE_ALIGNMENT_BRIDGE_OBLIGATION_v0",
    "EM_QFT_SHARED_DYNAMICS_WITNESS_REQUIRED_v0",
    "EM_QFT_RESIDUAL_UNIFICATION_SEMANTIC_BRIDGE_REQUIRED_v0",
}
REGISTRY_REQUIRED_EVIDENCE = REQUIRED_EVIDENCE | {
    "EM_QFT_SOURCE_CURRENT_SEMANTICS_BRIDGE_REQUIRED_v0",
    "EM_QFT_GAUGE_QUANTIZATION_SEMANTICS_BRIDGE_REQUIRED_v0",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _registry() -> dict:
    return json.loads(_read(REGISTRY_PATH))


def test_em_qft_protocol_row_records_blocker_without_promotion() -> None:
    text = _read(PROTOCOL_ROW_PATH)

    for token in {
        "em_qft_physics_blocker_protocol_row_v0",
        "SEAM-EM-QFT",
        CONSUMED_TARGET,
        PROTOCOL_SUCCESSOR_TARGET,
        PRIMARY_BLOCKER,
        SECONDARY_BLOCKER,
        "theorem_linked_shared_dynamics_discharge",
        "theorem_linked_residual_unification_discharge",
        "theorem_linked_interface_alignment_discharge",
        "em_qft_protocol_row_physics_incomplete_v0",
        "em_qft_protocol_row_seam_not_closed_v0",
        "em_qft_protocol_row_phase2_not_authorized_v0",
        "em_qft_protocol_row_master_action_not_promoted_v0",
        "em_qft_protocol_row_no_empirical_claim_v0",
        "em_qft_protocol_row_governance_manifest_not_enrolled_v0",
    } | REQUIRED_EVIDENCE:
        assert token in text

    assert "physics_complete := False" in text
    assert "em_qft_seam_closed := False" in text
    assert "phase2Authorized := False" in text
    assert "master_action_promoted := False" in text
    assert "empirical_claim := False" in text
    assert "governance_manifest_enrollment_authorized := False" in text


def test_frontier_uses_row_lookup_and_exposes_successor_target() -> None:
    assert_frontier_matches_registry()

    frontier_text = _read(CROSS_PILLAR_FRONTIER_PATH)

    assert "def crossPillarFrontierEntryByRow?" in frontier_text
    assert f'def previousLiveNextStrictTargetV0 : String :=\n  "{SOURCE_PROBABILITY_TARGET}"' in frontier_text
    assert f'def currentLiveNextStrictTargetV0 : String :=\n  "{LIVE_TARGET}"' in frontier_text
    assert f'next_strict_slice :=\n        "{LIVE_TARGET}"' in frontier_text

    review_files = [
        DERIVATION_DIR / "QMEvolutionPostBudgetCrossPillarReview.lean",
        DERIVATION_DIR / "QFTGRPostBudgetCrossPillarReview.lean",
        DERIVATION_DIR / "SRCosmologyPostBudgetCrossPillarReview.lean",
    ]
    for path in review_files:
        text = _read(path)
        assert "crossPillarFrontierEntryByRow?" in text
        assert "crossPillarClosureFrontierV0.drop" not in text


def test_loop_registry_and_public_surfaces_follow_em_qft_successor() -> None:
    assert_current_target_consistent()
    assert_public_surfaces_match_registry()

    payload = _registry()
    state = payload["current_target_state"]

    assert state["previous_live_next_target"] == SOURCE_PROBABILITY_TARGET
    assert state["live_next_target"] == LIVE_TARGET
    assert state["live_next_target_evidence"] == READINESS_EVIDENCE
    assert LIVE_TARGET in payload["next_strict_target_coverage"]
    assert AUDIT_TARGET in payload["next_strict_target_coverage"]
    assert REVIEW_TARGET in payload["next_strict_target_coverage"]
    assert CITATION_USAGE_TARGET in payload["next_strict_target_coverage"]
    assert PROTOCOL_SUCCESSOR_TARGET in payload["next_strict_target_coverage"]
    assert INTERFACE_TARGET in payload["next_strict_target_coverage"]
    assert POST_BUDGET_TARGET in payload["next_strict_target_coverage"]

    active = [item for item in payload["workstreams"] if item.get("status") == "active"]
    assert [item["workstream_id"] for item in active] == ["qm_stat_transport_residual"]
    assert active[0]["consumed_target"] == SOURCE_PROBABILITY_TARGET
    assert active[0]["authorized_next_strict_target"] == LIVE_TARGET
    assert active[0]["latest_surface"] == "QM_STAT_SOURCE_PROBABILITY_EXTRACTION_SEMANTICS_v0"

    em_qft = next(
        item for item in payload["workstreams"]
        if item["workstream_id"] == "em_qft_physics_blocker_extraction"
    )
    assert em_qft["status"] == "paused"
    assert em_qft["prior_consumed_target"] == PROTOCOL_SUCCESSOR_TARGET
    assert em_qft["consumed_target"] == INTERFACE_TARGET
    assert em_qft["authorized_next_strict_target"] == CITATION_USAGE_TARGET
    assert em_qft["latest_surface"] == "EM_QFT_INTERFACE_ALIGNMENT_SEMANTIC_BRIDGE_v0"
    assert em_qft["last_fresh_delta_kind"] == "counterexample"
    assert em_qft["primary_blocker"] == PRIMARY_BLOCKER
    assert em_qft["secondary_blocker"] == SECONDARY_BLOCKER
    assert set(em_qft["required_evidence"]) == REGISTRY_REQUIRED_EVIDENCE
    assert em_qft["post_budget_review_status"] == "completed"

    edges = {(edge["from"], edge["to"]) for edge in payload["dependency_edges"]}
    assert (
        "em_qft_physics_blocker_extraction",
        "em_qft_shared_dynamics_residual_unification_bridge",
    ) in edges
    assert (
        "em_qft_shared_dynamics_residual_unification_bridge",
        "em_qft_interface_alignment_semantic_bridge",
    ) in edges
    assert (
        "em_qft_interface_alignment_semantic_bridge",
        "em_qft_post_budget_review",
    ) in edges
    assert (
        "em_qft_post_budget_review",
        "master_action_dependency_frontier",
    ) in edges
    assert (
        "master_action_dependency_frontier",
        "master_action_retained_assumption_citation_usage",
    ) in edges

    for path in [REPO_ROOT / "README.md", REPO_ROOT / "State_of_the_Theory.md"]:
        assert f"CURRENT_LIVE_NEXT_TARGET_v0: {LIVE_TARGET}" in _read(path)


def test_em_qft_seam_registry_names_blocker_and_boundary() -> None:
    for path in [SEAM_REGISTRY_PATH, SEAM_INVENTORY_PATH]:
        text = _read(path)
        assert "SEAM_EM_QFT_GOVERNANCE_COMPLETE_v0: YES" in text
        assert "SEAM_EM_QFT_PHYSICS_COMPLETE_v0: NO" in text
        assert "SEAM_EM_QFT_PHYSICS_BLOCKER_v0: SHARED_DYNAMICS_AND_RESIDUAL_UNIFICATION_NOT_DISCHARGED" in text
        assert "SEAM_EM_QFT_SECONDARY_PHYSICS_BLOCKER_v0: INTERFACE_ALIGNMENT_SEMANTIC_BRIDGE_NOT_DISCHARGED" in text
        assert "SEAM_EM_QFT_SHARED_DYNAMICS_RESIDUAL_UNIFICATION_STATUS_v0: GOVERNANCE_WITNESS_AND_ZERO_RESIDUAL_ONLY_REFUTED_SUPPLIED_BRIDGE_PACKAGE_ROUTE_RETAINED" in text
        assert "SEAM_EM_QFT_INTERFACE_ALIGNMENT_STATUS_v0: INTERFACE_ALIGNMENT_ONLY_SOURCE_CURRENT_AND_GAUGE_QUANTIZATION_REFUTED_POST_BUDGET_REVIEW_REQUIRED" in text
        assert "SEAM_EM_QFT_CURRENT_PHYSICS_BLOCKER_TARGET_v0: PAUSED_AFTER_POST_BUDGET_REVIEW_NO_SAME_LANE_TARGET" in text
        assert f"MASTER_ACTION_CURRENT_CITATION_TARGET_v0: {LIVE_TARGET}" in text
        assert "NO_EM_QFT_SEAM_CLOSURE_NO_MASTER_ACTION_PROMOTION" in text


def test_em_qft_protocol_gate_is_focused_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_em_qft_physics_blocker_protocol_row_gate.py"
    )
