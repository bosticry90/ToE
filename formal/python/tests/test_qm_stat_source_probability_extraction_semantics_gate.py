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
    workstream,
)


REPO_ROOT = find_repo_root(Path(__file__))
SOURCE_PROBABILITY_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QM_STAT_SourceProbabilityExtractionSemantics.lean"
)
READINESS_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMSTATTransportSemanticsProtocolRowReadinessReview.lean"
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

SOURCE_TARGET = "derive_or_refute_qm_stat_source_probability_extraction_semantics"
RESULT_REVIEW_TARGET = "review_qm_stat_source_probability_extraction_semantics_result"
SURFACE_ID = "QM_STAT_SOURCE_PROBABILITY_EXTRACTION_SEMANTICS_v0"
FRESH_DELTA_ID = (
    "QM_STAT_SOURCE_PROBABILITY_EXTRACTION_CONTRACT_ONLY_COUNTEREXAMPLE_FRESH_DELTA_v0"
)
RETAINED_BLOCKER = (
    "PHASE1-BLOCKER-QMSTAT-SOURCE-PROBABILITY-EXTRACTION-SEMANTICS-RETAINED"
)
SOURCE_PROBABILITY_EVIDENCE = str(SOURCE_PROBABILITY_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
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


def test_source_probability_semantics_surface_records_route_and_counterexample() -> None:
    text = _read(SOURCE_PROBABILITY_PATH)

    for token in {
        SURFACE_ID,
        SOURCE_TARGET,
        RESULT_REVIEW_TARGET,
        RETAINED_BLOCKER,
        FRESH_DELTA_ID,
        "counterexample",
        "QMEvolutionSourceProbabilityExtractionData",
        "sourceStructureOfQMEvolutionSourceProbabilityExtraction",
        "supplied_source_probability_extraction_constructs_source_structure_v0",
        "qm_evolution_contract_does_not_force_source_probability_extraction_v0",
        "qm_stat_source_probability_extraction_supplied_route_available_v0",
        "qm_stat_source_probability_extraction_contract_only_refuted_v0",
        "qm_stat_source_probability_extraction_not_contract_only_v0",
        "qm_stat_source_probability_extraction_retained_as_supplied_v0",
        "qm_stat_source_probability_extraction_selected_next_target_v0",
        "qm_stat_source_probability_extraction_frontier_target_v0",
    }:
        assert token in text


def test_source_probability_slice_preserves_fail_closed_boundaries() -> None:
    text = _read(SOURCE_PROBABILITY_PATH)

    for theorem in {
        "qm_stat_source_probability_extraction_target_entropy_not_authorized_v0",
        "qm_stat_source_probability_extraction_transport_map_not_authorized_v0",
        "qm_stat_source_probability_extraction_coarse_graining_not_authorized_v0",
        "qm_stat_source_probability_extraction_residual_closure_not_authorized_v0",
        "qm_stat_source_probability_extraction_no_seam_closure_v0",
        "qm_stat_source_probability_extraction_no_stat_mechanics_claim_v0",
        "qm_stat_source_probability_extraction_phase2_not_authorized_v0",
        "qm_stat_source_probability_extraction_master_action_not_promoted_v0",
        "qm_stat_source_probability_extraction_no_empirical_claim_v0",
        "qm_stat_source_probability_extraction_governance_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_frontier_and_aggregate_rotate_to_source_probability_result_review() -> None:
    assert_frontier_matches_registry()
    aggregate_text = _read(AGGREGATE_PATH)
    frontier_text = _read(FRONTIER_PATH)

    assert "import ToeFormal.Bridges.QM_STAT_SourceProbabilityExtractionSemantics" in aggregate_text
    assert "source-probability extraction supplied route and contract-only obstruction" in frontier_text


def test_loop_registry_tracks_source_probability_result_review_only() -> None:
    assert_current_target_consistent()
    payload = _registry()

    assert RESULT_REVIEW_TARGET in payload["next_strict_target_coverage"]
    assert RETAINED_BLOCKER in payload["retained_blocker_coverage"]

    qm_stat = workstream("qm_stat_transport_residual", payload)
    assert qm_stat["retained_blocker"] == RETAINED_BLOCKER
    assert qm_stat["authorization_evidence"] == SOURCE_PROBABILITY_EVIDENCE
    assert qm_stat["consumed_target"] == SOURCE_TARGET
    assert qm_stat["prior_surface"] == "qm_stat_transport_semantics_protocol_row_readiness_review_v0"
    assert qm_stat["latest_surface"] == SURFACE_ID
    assert qm_stat["authorized_next_strict_target"] == RESULT_REVIEW_TARGET
    assert qm_stat["same_lane_continuation"] == "post_source_probability_slice_review_only"
    assert qm_stat["bounded_source_probability_slice_authorized"] == "completed"
    assert (
        qm_stat["source_probability_extraction_semantics_status"]
        == "supplied_route_available_contract_only_refuted_retained_as_semantic_assumption"
    )
    assert qm_stat["source_probability_extraction_supplied_route_available"] == "yes"
    assert qm_stat["source_probability_extraction_contract_only_refuted"] == "yes"
    assert qm_stat["source_probability_extraction_derived_from_contract_alone"] == "no"
    assert qm_stat["theorem_work_authorized"] == "no_pending_source_probability_result_review"
    assert (
        qm_stat["source_probability_extraction_obligation"]
        == "retained_as_supplied_semantics_not_contract_derived"
    )
    assert qm_stat["target_entropy_semantics_authorized"] == "no"
    assert qm_stat["transport_map_semantics_authorized"] == "no"
    assert qm_stat["coarse_graining_irreversibility_authorized"] == "no"
    assert qm_stat["residual_package_semantic_closure_authorized"] == "no"

    master_action = _workstream(payload, "master_action_dependency_frontier")
    assert master_action["status"] == "paused"
    assert master_action["source_probability_extraction_evidence"] == SOURCE_PROBABILITY_EVIDENCE
    assert master_action["source_probability_extraction_status"] == (
        "completed_supplied_route_available_contract_only_refuted"
    )
    assert master_action["authorized_next_strict_target"] == RESULT_REVIEW_TARGET
    assert master_action["same_lane_continuation"] == "post_source_probability_slice_review_only"
    assert master_action["theorem_work_authorized"] == "no_pending_source_probability_result_review"

    edges = {(edge["from"], edge["to"]) for edge in payload["dependency_edges"]}
    assert (
        "qm_stat_transport_semantics_protocol_row_readiness_review",
        "qm_stat_source_probability_extraction_semantics",
    ) in edges
    assert (
        "qm_stat_source_probability_extraction_semantics",
        "qm_stat_source_probability_extraction_semantics_result_review",
    ) in edges


def test_public_surfaces_and_manifest_boundary_are_synchronized() -> None:
    assert_public_surfaces_match_registry()
    for path in [README_PATH, STATE_PATH, ROADMAP_PATH, STRICT_MAP_PATH]:
        text = _read(path)
        assert "QM_STAT_SourceProbabilityExtractionSemantics.lean" in text
        assert "CONTRACT_ONLY" in text or "contract-only" in text

    for path in [SEAM_REGISTRY_PATH, SEAM_INVENTORY_PATH]:
        text = _read(path)
        assert "QM_STAT_SOURCE_PROBABILITY_EXTRACTION_SEMANTICS_v0" in text
        assert RESULT_REVIEW_TARGET in text

    inventory_text = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-QMSTAT-SOURCE-PROBABILITY-EXTRACTION-SEMANTICS-v0" in inventory_text
    assert SOURCE_PROBABILITY_EVIDENCE in inventory_text
    assert READINESS_EVIDENCE in inventory_text
    assert_focused_gate_not_manifest_enrolled(
        "test_qm_stat_source_probability_extraction_semantics_gate.py"
    )
