from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
USAGE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionRetainedAssumptionCitationUsage.lean"
)
AUDIT_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionCitationLanguageAudit.lean"
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
MASTER_ACTION_FRONTIER_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionDependencyFrontier.lean"
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

CONSUMED_TARGET = "cite_only_bounded_retained_assumptions"
AUDIT_TARGET = "audit_master_action_citation_language_against_retained_boundaries"
REVIEW_TARGET = "review_master_action_dependency_graph_after_citation_language_audit"
PRIORITIZATION_TARGET = "prioritize_retained_blockers_after_master_action_dependency_graph_review"
PROTOCOL_TARGET = "prepare_qm_stat_transport_semantics_retained_blocker_protocol_row"
READINESS_REVIEW_TARGET = "review_qm_stat_transport_semantics_protocol_row_readiness"
SOURCE_PROBABILITY_TARGET = "derive_or_refute_qm_stat_source_probability_extraction_semantics"
LIVE_TARGET = "review_qm_stat_source_probability_extraction_semantics_result"
READINESS_EVIDENCE = "formal/toe_formal/ToeFormal/Bridges/QM_STAT_SourceProbabilityExtractionSemantics.lean"
SURFACE_ID = "master_action_retained_assumption_citation_usage_v0"
USAGE_EVIDENCE = str(USAGE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
AUDIT_EVIDENCE = str(AUDIT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
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


def _workstream(payload: dict[str, Any], workstream_id: str) -> dict[str, Any]:
    for workstream in payload["workstreams"]:
        if workstream["workstream_id"] == workstream_id:
            return workstream
    raise AssertionError(f"Missing workstream: {workstream_id}")


def test_master_action_citation_usage_records_bounded_usage_only() -> None:
    text = _read(USAGE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        AUDIT_TARGET,
        "masterActionCitationBoundariesV0",
        "master_action_citation_usage_consumes_live_target_v0",
        "master_action_citation_usage_selected_next_target_v0",
        "master_action_citation_usage_frontier_target_v0",
        "master_action_citation_usage_reuses_frontier_ids_v0",
        "master_action_citation_usage_boundary_count_v0",
        "master_action_citation_usage_boundaries_reused_v0",
        "master_action_citation_usage_only_bounded_retained_assumptions_v0",
        "master_action_citation_usage_forbidden_scopes_carried_v0",
        "master_action_citation_usage_dependency_classes_not_changed_v0",
    }:
        assert token in text

    for token in {
        "master_action_citation_usage_no_seam_closure_v0",
        "master_action_citation_usage_phase2_not_authorized_v0",
        "master_action_citation_usage_master_action_not_promoted_v0",
        "master_action_citation_usage_no_empirical_claim_v0",
        "master_action_citation_usage_governance_manifest_not_enrolled_v0",
    }:
        assert token in text


def test_frontier_and_aggregate_advance_after_citation_language_audit() -> None:
    aggregate_text = _read(AGGREGATE_PATH)
    frontier_text = _read(FRONTIER_PATH)
    master_action_text = _read(MASTER_ACTION_FRONTIER_PATH)

    assert "import ToeFormal.Derivation.MasterActionRetainedAssumptionCitationUsage" in aggregate_text
    assert "import ToeFormal.Derivation.MasterActionCitationLanguageAudit" in aggregate_text
    assert "import ToeFormal.Derivation.MasterActionDependencyGraphReview" in aggregate_text
    assert (
        "import ToeFormal.Derivation.MasterActionRetainedBlockerPrioritizationReview"
        in aggregate_text
    )
    assert (
        "import ToeFormal.Derivation.QMSTATTransportSemanticsRetainedBlockerProtocolRow"
        in aggregate_text
    )
    assert f'def previousLiveNextStrictTargetV0 : String :=\n  "{SOURCE_PROBABILITY_TARGET}"' in frontier_text
    assert f'def currentLiveNextStrictTargetV0 : String :=\n  "{LIVE_TARGET}"' in frontier_text
    assert f'next_strict_slice :=\n        "{LIVE_TARGET}"' in frontier_text
    assert "source-probability extraction supplied route and contract-only obstruction" in frontier_text
    assert "def masterActionCitationBoundariesV0" in master_action_text
    assert "theorem master_action_citation_boundaries_length_v0" in master_action_text


def test_loop_registry_tracks_citation_usage_as_current_master_action_lane() -> None:
    payload = _registry()
    state = payload["current_target_state"]

    assert state["previous_live_next_target"] == SOURCE_PROBABILITY_TARGET
    assert state["live_next_target"] == LIVE_TARGET
    assert state["live_next_target_evidence"] == READINESS_EVIDENCE
    assert state["active_lane"] == "qm_stat_transport_residual"
    assert LIVE_TARGET in payload["next_strict_target_coverage"]

    active = [item for item in payload["workstreams"] if item.get("status") == "active"]
    assert [item["workstream_id"] for item in active] == ["qm_stat_transport_residual"]
    workstream = active[0]
    assert workstream["authorization_evidence"] == READINESS_EVIDENCE
    assert workstream["consumed_target"] == SOURCE_PROBABILITY_TARGET
    assert workstream["prior_surface"] == "qm_stat_transport_semantics_protocol_row_readiness_review_v0"
    assert workstream["latest_surface"] == "QM_STAT_SOURCE_PROBABILITY_EXTRACTION_SEMANTICS_v0"
    assert workstream["authorized_next_strict_target"] == LIVE_TARGET
    assert workstream["same_lane_continuation"] == "post_source_probability_slice_review_only"

    edges = {(edge["from"], edge["to"]) for edge in payload["dependency_edges"]}
    assert (
        "master_action_dependency_frontier",
        "master_action_retained_assumption_citation_usage",
    ) in edges
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
    assert (
        "master_action_retained_blocker_prioritization_review",
        "qm_stat_transport_semantics_retained_blocker_protocol_row",
    ) in edges


def test_public_surfaces_expose_usage_and_manifest_remains_unchanged() -> None:
    for path in [README_PATH, STATE_PATH, ROADMAP_PATH, STRICT_MAP_PATH]:
        text = _read(path)
        assert LIVE_TARGET in text, f"{path} missing live target"

    for path in [README_PATH, ROADMAP_PATH]:
        text = _read(path)
        assert "retained-assumption citation usage" in text.lower()

    for path in [STATE_PATH, STRICT_MAP_PATH, SEAM_REGISTRY_PATH, SEAM_INVENTORY_PATH]:
        assert "MasterActionRetainedAssumptionCitationUsage.lean" in _read(path)
        assert "MasterActionCitationLanguageAudit.lean" in _read(path)
        assert "MasterActionDependencyGraphReview.lean" in _read(path)
        assert "MasterActionRetainedBlockerPrioritizationReview.lean" in _read(path)
        assert "QMSTATTransportSemanticsRetainedBlockerProtocolRow.lean" in _read(path)

    inventory_text = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-MASTER-ACTION-RETAINED-ASSUMPTION-CITATION-USAGE-v0" in inventory_text
    assert "INV-MATH-MASTER-ACTION-RETAINED-BLOCKER-PRIORITIZATION-REVIEW-v0" in inventory_text
    assert "INV-MATH-QMSTAT-TRANSPORT-SEMANTICS-PROTOCOL-ROW-v0" in inventory_text
    assert USAGE_EVIDENCE in inventory_text
    assert PRIORITIZATION_EVIDENCE in inventory_text
    assert PROTOCOL_EVIDENCE in inventory_text
    assert "test_master_action_retained_assumption_citation_usage_gate.py" not in _read(
        GOVERNANCE_MANIFEST_PATH
    )
