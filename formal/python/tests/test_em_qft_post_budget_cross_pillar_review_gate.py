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
    / "EMQFTPostBudgetCrossPillarReview.lean"
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
MASTER_ACTION_FRONTIER_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionDependencyFrontier.lean"
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
MATH_PHYSICS_INVENTORY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
)

CONSUMED_TARGET = "em_qft_post_budget_cross_pillar_review"
CITATION_USAGE_TARGET = "cite_only_bounded_retained_assumptions"
AUDIT_TARGET = "audit_master_action_citation_language_against_retained_boundaries"
REVIEW_TARGET = "review_master_action_dependency_graph_after_citation_language_audit"
PRIORITIZATION_TARGET = "prioritize_retained_blockers_after_master_action_dependency_graph_review"
PROTOCOL_TARGET = "prepare_qm_stat_transport_semantics_retained_blocker_protocol_row"
READINESS_REVIEW_TARGET = "review_qm_stat_transport_semantics_protocol_row_readiness"
LIVE_TARGET = "derive_or_refute_qm_stat_source_probability_extraction_semantics"
READINESS_EVIDENCE = "formal/toe_formal/ToeFormal/Derivation/QMSTATTransportSemanticsProtocolRowReadinessReview.lean"
SURFACE_ID = "em_qft_post_budget_cross_pillar_review_v0"
REVIEW_EVIDENCE = str(REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
USAGE_EVIDENCE = str(MASTER_ACTION_CITATION_USAGE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
AUDIT_EVIDENCE = str(MASTER_ACTION_CITATION_AUDIT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REVIEW_GRAPH_EVIDENCE = str(
    PROTOCOL_ROW_PATH.relative_to(REPO_ROOT)
).replace("\\", "/")
RETAINED_BLOCKER = "PHASE1-BLOCKER-EMQFT-INTERFACE-ALIGNMENT-SEMANTIC-BRIDGE-RETAINED"


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


def test_em_qft_post_budget_review_records_pause_and_rotation_decision() -> None:
    text = _read(REVIEW_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        CITATION_USAGE_TARGET,
        "rotate_to_master_action_citation_boundary",
        "em_qft_post_budget_attempt_budget_reached_v0",
        "em_qft_post_budget_interface_alignment_counterexample_recorded_v0",
        "em_qft_post_budget_imported_interface_attempt_budget_reached_v0",
        "em_qft_post_budget_source_current_still_required_v0",
        "em_qft_post_budget_gauge_quantization_still_required_v0",
        "em_qft_post_budget_same_lane_not_authorized_v0",
        "em_qft_post_budget_source_current_slice_not_authorized_v0",
        "em_qft_post_budget_gauge_quantization_slice_not_authorized_v0",
        "em_qft_post_budget_master_dependency_class_not_changed_v0",
        "em_qft_post_budget_required_for_coherence_retained_v0",
        "em_qft_post_budget_selects_master_action_citation_route_v0",
        "em_qft_post_budget_selected_strict_target_v0",
        "em_qft_post_budget_master_action_frontier_target_v0",
        "em_qft_post_budget_em_qft_frontier_row_rotates_to_master_action_v0",
        "em_qft_post_budget_master_action_dependency_frontier_citation_only_v0",
    }:
        assert token in text

    for token in {
        "em_qft_post_budget_phase2_not_authorized_v0",
        "em_qft_post_budget_em_qft_seam_not_closed_v0",
        "em_qft_post_budget_master_action_not_promoted_v0",
        "em_qft_post_budget_no_empirical_claim_v0",
        "em_qft_post_budget_governance_manifest_not_enrolled_v0",
    }:
        assert token in text


def test_frontier_aggregate_and_master_dependency_surface_follow_review() -> None:
    aggregate_text = _read(AGGREGATE_PATH)
    frontier_text = _read(FRONTIER_PATH)
    master_action_text = _read(MASTER_ACTION_FRONTIER_PATH)

    assert "import ToeFormal.Derivation.EMQFTPostBudgetCrossPillarReview" in aggregate_text
    assert "import ToeFormal.Derivation.MasterActionRetainedAssumptionCitationUsage" in aggregate_text
    assert "import ToeFormal.Derivation.MasterActionCitationLanguageAudit" in aggregate_text
    assert "import ToeFormal.Derivation.MasterActionDependencyGraphReview" in aggregate_text
    assert (
        "import ToeFormal.Derivation.QMSTATTransportSemanticsRetainedBlockerProtocolRow"
        in aggregate_text
    )
    assert f'def previousLiveNextStrictTargetV0 : String :=\n  "{READINESS_REVIEW_TARGET}"' in frontier_text
    assert f'def currentLiveNextStrictTargetV0 : String :=\n  "{LIVE_TARGET}"' in frontier_text
    assert f'next_strict_slice :=\n        "{LIVE_TARGET}"' in frontier_text
    assert "EM-QFT interface-alignment semantic bridge obstruction plus post-budget review" in frontier_text
    assert "SEAM_EM_QFT_PHYSICS_COMPLETE_v0:NO" in master_action_text
    assert "post_budget_retained" in master_action_text
    assert "source_current" in master_action_text
    assert "gauge_quantization" in master_action_text


def test_registry_rotates_to_master_action_dependency_frontier() -> None:
    payload = _registry()
    state = payload["current_target_state"]

    assert state["previous_live_next_target"] == READINESS_REVIEW_TARGET
    assert state["live_next_target"] == LIVE_TARGET
    assert state["live_next_target_evidence"] == READINESS_EVIDENCE
    assert state["active_lane"] == "qm_stat_transport_residual"
    assert "em_qft_physics_blocker_extraction" in state["paused_lanes"]

    active = [item for item in payload["workstreams"] if item.get("status") == "active"]
    assert [item["workstream_id"] for item in active] == ["qm_stat_transport_residual"]
    assert active[0]["authorization_evidence"] == READINESS_EVIDENCE
    assert active[0]["consumed_target"] == READINESS_REVIEW_TARGET
    assert active[0]["latest_surface"] == "qm_stat_transport_semantics_protocol_row_readiness_review_v0"
    assert active[0]["authorized_next_strict_target"] == LIVE_TARGET
    assert active[0]["same_lane_continuation"] == "authorized_bounded_source_probability_extraction_slice"

    em_qft = _workstream(payload, "em_qft_physics_blocker_extraction")
    assert em_qft["status"] == "paused"
    assert em_qft["retained_blocker"] == RETAINED_BLOCKER
    assert em_qft["post_budget_review_status"] == "completed"
    assert em_qft["post_budget_review_evidence"] == REVIEW_EVIDENCE
    assert em_qft["post_budget_review_decision"] == (
        "pause_same_lane_and_rotate_to_master_action_citation_boundary"
    )
    assert em_qft["source_current_bridge_slice_authorized"] == "not_authorized"
    assert em_qft["gauge_quantization_bridge_slice_authorized"] == "not_authorized"
    assert em_qft["master_dependency_class_changed"] == "no"
    assert em_qft["master_action_dependency_class"] == "required_for_coherence"

    edges = {(edge["from"], edge["to"]) for edge in payload["dependency_edges"]}
    assert ("em_qft_post_budget_review", "master_action_dependency_frontier") in edges


def test_public_surfaces_expose_citation_target_without_manifest_enrollment() -> None:
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

    for path in [STATE_PATH, STRICT_MAP_PATH, SEAM_REGISTRY_PATH, SEAM_INVENTORY_PATH]:
        assert "EMQFTPostBudgetCrossPillarReview.lean" in _read(
            path
        ), f"{path} missing review surface"

    inventory_text = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-EM-QFT-POST-BUDGET-CROSS-PILLAR-REVIEW-v0" in inventory_text
    assert REVIEW_EVIDENCE in inventory_text
    assert "EM_QFT_POST_BUDGET_CROSS_PILLAR_REVIEW_v0" in _read(STATE_PATH)
    assert "SEAM_EM_QFT_POST_BUDGET_STATUS_v0" in _read(SEAM_REGISTRY_PATH)
    assert "test_em_qft_post_budget_cross_pillar_review_gate.py" not in _read(
        GOVERNANCE_MANIFEST_PATH
    )
