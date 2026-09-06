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
BRIDGE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "EM_QFT_SharedDynamicsResidualUnificationBridge.lean"
)
INTERFACE_BRIDGE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "EM_QFT_InterfaceAlignmentSemanticBridge.lean"
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
PROTOCOL_ROW_PATH = (
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

CONSUMED_TARGET = "derive_or_refute_em_qft_shared_dynamics_residual_unification_bridge"
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
SURFACE_ID = "EM_QFT_SHARED_DYNAMICS_RESIDUAL_UNIFICATION_BRIDGE_v0"
FRESH_DELTA_ID = (
    "EM_QFT_SHARED_DYNAMICS_RESIDUAL_UNIFICATION_BRIDGE_COUNTEREXAMPLE_FRESH_DELTA_v0"
)
RETAINED_BLOCKER = (
    "PHASE1-BLOCKER-EMQFT-SHARED-DYNAMICS-RESIDUAL-UNIFICATION-BRIDGE-RETAINED"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _registry() -> dict:
    return json.loads(_read(REGISTRY_PATH))


def test_shared_dynamics_bridge_surface_records_counterexample_and_conditional_route() -> None:
    text = _read(BRIDGE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        INTERFACE_TARGET,
        FRESH_DELTA_ID,
        RETAINED_BLOCKER,
        "counterexample",
        "EMQFTSharedDynamicsResidualUnificationPackage",
        "supplied_shared_dynamics_residual_semantics_construct_bridge_package_v0",
        "zero_residual_package_does_not_force_em_qft_full_bridge_semantics_v0",
        "governance_witness_only_does_not_force_shared_dynamics_bridge_v0",
        "em_qft_shared_dynamics_interface_alignment_required_v0",
        "em_qft_shared_dynamics_selected_next_target_v0",
    }:
        assert token in text


def test_shared_dynamics_bridge_preserves_nonpromotion_boundaries() -> None:
    text = _read(BRIDGE_PATH)

    for token in {
        "em_qft_seam_closed := False",
        "phase2Authorized := False",
        "master_action_promoted := False",
        "empirical_claim := False",
        "governance_manifest_enrollment_authorized := False",
        "em_qft_shared_dynamics_no_seam_closure_v0",
        "em_qft_shared_dynamics_phase2_not_authorized_v0",
        "em_qft_shared_dynamics_master_action_not_promoted_v0",
        "em_qft_shared_dynamics_no_empirical_claim_v0",
        "em_qft_shared_dynamics_governance_manifest_not_enrolled_v0",
    }:
        assert token in text


def test_frontier_and_aggregate_advance_after_post_budget_review() -> None:
    assert_frontier_matches_registry()

    aggregate_text = _read(AGGREGATE_PATH)
    frontier_text = _read(FRONTIER_PATH)

    assert "import ToeFormal.Bridges.EM_QFT_SharedDynamicsResidualUnificationBridge" in aggregate_text
    assert "import ToeFormal.Bridges.EM_QFT_InterfaceAlignmentSemanticBridge" in aggregate_text
    assert "import ToeFormal.Derivation.EMQFTPostBudgetCrossPillarReview" in aggregate_text
    assert "import ToeFormal.Derivation.MasterActionRetainedAssumptionCitationUsage" in aggregate_text
    assert "import ToeFormal.Derivation.MasterActionCitationLanguageAudit" in aggregate_text
    assert "import ToeFormal.Derivation.MasterActionDependencyGraphReview" in aggregate_text
    assert f'def previousLiveNextStrictTargetV0 : String :=\n  "{SOURCE_PROBABILITY_TARGET}"' in frontier_text
    assert f'def currentLiveNextStrictTargetV0 : String :=\n  "{LIVE_TARGET}"' in frontier_text
    assert "PHASE1-BLOCKER-EMQFT-INTERFACE-ALIGNMENT-SEMANTIC-BRIDGE-RETAINED" in frontier_text


def test_registry_tracks_focused_em_qft_bridge_slice() -> None:
    assert_current_target_consistent()

    payload = _registry()
    state = payload["current_target_state"]

    assert state["previous_live_next_target"] == SOURCE_PROBABILITY_TARGET
    assert state["live_next_target"] == LIVE_TARGET
    assert state["live_next_target_evidence"] == READINESS_EVIDENCE

    assert RETAINED_BLOCKER in payload["retained_blocker_coverage"]
    assert CONSUMED_TARGET in payload["next_strict_target_coverage"]
    assert INTERFACE_TARGET in payload["next_strict_target_coverage"]
    assert POST_BUDGET_TARGET in payload["next_strict_target_coverage"]
    assert CITATION_USAGE_TARGET in payload["next_strict_target_coverage"]
    assert AUDIT_TARGET in payload["next_strict_target_coverage"]
    assert REVIEW_TARGET in payload["next_strict_target_coverage"]
    assert LIVE_TARGET in payload["next_strict_target_coverage"]

    workstream = next(
        item for item in payload["workstreams"]
        if item["workstream_id"] == "em_qft_physics_blocker_extraction"
    )
    assert workstream["status"] == "paused"
    assert workstream["retained_blocker"] == "PHASE1-BLOCKER-EMQFT-INTERFACE-ALIGNMENT-SEMANTIC-BRIDGE-RETAINED"
    assert workstream["consumed_target"] == INTERFACE_TARGET
    assert workstream["authorized_next_strict_target"] == CITATION_USAGE_TARGET
    assert workstream["latest_surface"] == "EM_QFT_INTERFACE_ALIGNMENT_SEMANTIC_BRIDGE_v0"
    assert workstream["last_fresh_delta_kind"] == "counterexample"
    assert workstream["last_fresh_delta_id"] == "EM_QFT_INTERFACE_ALIGNMENT_SEMANTIC_BRIDGE_COUNTEREXAMPLE_FRESH_DELTA_v0"
    assert workstream["governance_witness_only_bridge_closure"] == "refuted"
    assert workstream["zero_residual_only_bridge_closure"] == "refuted"
    assert workstream["interface_alignment_only_source_current_closure"] == "refuted"
    assert workstream["post_budget_review_status"] == "completed"


def test_docs_expose_next_target_without_manifest_enrollment() -> None:
    assert_public_surfaces_match_registry()

    for path in [
        README_PATH,
        STATE_PATH,
        ROADMAP_PATH,
        STRICT_MAP_PATH,
        SEAM_REGISTRY_PATH,
        SEAM_INVENTORY_PATH,
    ]:
        text = _read(path)
        assert LIVE_TARGET in text, f"{path} missing live target"

    assert SURFACE_ID in _read(STATE_PATH)
    assert SURFACE_ID in _read(STRICT_MAP_PATH)
    assert "SEAM_EM_QFT_SHARED_DYNAMICS_RESIDUAL_UNIFICATION_STATUS_v0" in _read(SEAM_REGISTRY_PATH)
    assert "SEAM_EM_QFT_INTERFACE_ALIGNMENT_STATUS_v0" in _read(SEAM_REGISTRY_PATH)
    assert_focused_gate_not_manifest_enrolled(
        "test_em_qft_shared_dynamics_residual_unification_bridge_gate.py"
    )
