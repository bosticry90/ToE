from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
AUDIT_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionCitationLanguageAudit.lean"
)
USAGE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionRetainedAssumptionCitationUsage.lean"
)
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
CANDIDATE_MASTER_ACTION_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_CANDIDATE_MASTER_ACTION_v0.md"
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

CONSUMED_TARGET = "audit_master_action_citation_language_against_retained_boundaries"
REVIEW_TARGET = "review_master_action_dependency_graph_after_citation_language_audit"
PRIORITIZATION_TARGET = "prioritize_retained_blockers_after_master_action_dependency_graph_review"
LIVE_TARGET = "prepare_qm_stat_transport_semantics_retained_blocker_protocol_row"
SURFACE_ID = "master_action_citation_language_audit_v0"
AUDIT_EVIDENCE = str(AUDIT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REVIEW_EVIDENCE = str(REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
PRIORITIZATION_EVIDENCE = str(PRIORITIZATION_REVIEW_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _registry() -> dict[str, Any]:
    return json.loads(_read(REGISTRY_PATH))


def test_master_action_citation_language_audit_records_forbidden_language_classes() -> None:
    text = _read(AUDIT_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        REVIEW_TARGET,
        "MasterActionForbiddenLanguageClass",
        "closure_implication",
        "phase2_authorization",
        "seam_completion",
        "empirical_validation",
        "proof_complete_beyond_retained_assumptions",
        "master_action_promotion",
        "governance_manifest_enrollment",
        "master_action_citation_language_audit_forbidden_class_count_v0",
        "master_action_citation_language_audit_consumes_live_target_v0",
        "master_action_citation_language_audit_selected_next_target_v0",
        "master_action_citation_language_audit_frontier_target_v0",
        "master_action_citation_language_audit_preserves_usage_ids_v0",
    }:
        assert token in text


def test_audit_preserves_no_claim_and_nonpromotion_theorems() -> None:
    text = _read(AUDIT_PATH)

    for token in {
        "master_action_citation_language_audit_no_closure_implication_v0",
        "master_action_citation_language_audit_no_phase2_language_v0",
        "master_action_citation_language_audit_no_seam_completion_v0",
        "master_action_citation_language_audit_no_empirical_validation_v0",
        "master_action_citation_language_audit_no_proof_complete_beyond_retained_v0",
        "master_action_citation_language_audit_no_promotion_language_v0",
        "master_action_citation_language_audit_no_seam_closure_v0",
        "master_action_citation_language_audit_phase2_not_authorized_v0",
        "master_action_citation_language_audit_master_action_not_promoted_v0",
        "master_action_citation_language_audit_no_empirical_claim_v0",
        "master_action_citation_language_audit_governance_manifest_not_enrolled_v0",
    }:
        assert token in text

    candidate_text = _read(CANDIDATE_MASTER_ACTION_PATH)
    for token in {
        "working-form artifact only",
        "explicitly non-canonical",
        "does not assert external truth by itself",
        "does not promote theorem labels by itself",
        "TOE_CANONICAL_ACTION_PROMOTION_STATUS_v0: BLOCKED_PENDING_CRITERIA",
    }:
        assert token in candidate_text


def test_frontier_aggregate_and_usage_surface_rotate_to_post_audit_review() -> None:
    aggregate_text = _read(AGGREGATE_PATH)
    frontier_text = _read(FRONTIER_PATH)
    usage_text = _read(USAGE_PATH)
    review_text = _read(REVIEW_PATH)

    assert "import ToeFormal.Derivation.MasterActionCitationLanguageAudit" in aggregate_text
    assert "import ToeFormal.Derivation.MasterActionDependencyGraphReview" in aggregate_text
    assert (
        "import ToeFormal.Derivation.MasterActionRetainedBlockerPrioritizationReview"
        in aggregate_text
    )
    assert f'def previousLiveNextStrictTargetV0 : String :=\n  "{PRIORITIZATION_TARGET}"' in frontier_text
    assert f'def currentLiveNextStrictTargetV0 : String :=\n  "{LIVE_TARGET}"' in frontier_text
    assert f'next_strict_slice :=\n        "{LIVE_TARGET}"' in frontier_text
    assert "master-action retained-blocker prioritization review" in frontier_text
    assert "master_action_citation_usage_selected_next_target_v0" in usage_text
    assert "master_action_citation_usage_frontier_target_v0" in usage_text
    assert "master_action_dependency_graph_review_consumes_live_target_v0" in review_text


def test_loop_registry_tracks_citation_language_audit_as_current_surface() -> None:
    payload = _registry()
    state = payload["current_target_state"]

    assert state["previous_live_next_target"] == PRIORITIZATION_TARGET
    assert state["live_next_target"] == LIVE_TARGET
    assert state["live_next_target_evidence"] == PRIORITIZATION_EVIDENCE
    assert state["active_lane"] == "master_action_dependency_frontier"
    assert LIVE_TARGET in payload["next_strict_target_coverage"]

    active = [item for item in payload["workstreams"] if item.get("status") == "active"]
    assert [item["workstream_id"] for item in active] == ["master_action_dependency_frontier"]
    workstream = active[0]
    assert workstream["authorization_evidence"] == PRIORITIZATION_EVIDENCE
    assert workstream["consumed_target"] == PRIORITIZATION_TARGET
    assert workstream["prior_consumed_target"] == REVIEW_TARGET
    assert workstream["prior_surface"] == "master_action_dependency_graph_review_v0"
    assert workstream["latest_surface"] == "master_action_retained_blocker_prioritization_review_v0"
    assert workstream["citation_language_audit_status"] == "completed"
    assert workstream["dependency_graph_review_status"] == "completed"
    assert workstream["forbidden_language_class_count"] == 7
    assert workstream["dependency_classes_changed"] == "no"
    assert workstream["authorized_next_strict_target"] == LIVE_TARGET
    assert workstream["same_lane_continuation"] == "protocol_row_preparation_only"

    edges = {(edge["from"], edge["to"]) for edge in payload["dependency_edges"]}
    assert (
        "master_action_retained_assumption_citation_usage",
        "master_action_citation_language_audit",
    ) in edges
    assert (
        "master_action_citation_language_audit",
        "master_action_dependency_graph_review",
    ) in edges
    assert (
        "master_action_dependency_graph_review",
        "master_action_retained_blocker_prioritization_review",
    ) in edges


def test_public_surfaces_expose_audit_and_manifest_remains_unchanged() -> None:
    for path in [README_PATH, STATE_PATH, ROADMAP_PATH, STRICT_MAP_PATH]:
        text = _read(path)
        assert LIVE_TARGET in text, f"{path} missing live target"

    for path in [STATE_PATH, STRICT_MAP_PATH, SEAM_REGISTRY_PATH, SEAM_INVENTORY_PATH]:
        assert "MasterActionCitationLanguageAudit.lean" in _read(path)
        assert "MasterActionDependencyGraphReview.lean" in _read(path)
        assert "MasterActionRetainedBlockerPrioritizationReview.lean" in _read(path)

    inventory_text = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-MASTER-ACTION-CITATION-LANGUAGE-AUDIT-v0" in inventory_text
    assert "INV-MATH-MASTER-ACTION-RETAINED-BLOCKER-PRIORITIZATION-REVIEW-v0" in inventory_text
    assert AUDIT_EVIDENCE in inventory_text
    assert PRIORITIZATION_EVIDENCE in inventory_text
    assert "test_master_action_citation_language_audit_gate.py" not in _read(
        GOVERNANCE_MANIFEST_PATH
    )
