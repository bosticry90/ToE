from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_current_target_consistent,
    assert_focused_gate_not_manifest_enrolled,
    assert_forbidden_promotions_closed,
    assert_frontier_matches_registry,
    assert_public_surfaces_match_registry,
)


REPO_ROOT = find_repo_root(Path(__file__))
READINESS_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRSourceMapSemanticsProtocolRowReadinessReview.lean"
)
PROTOCOL_ROW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRSourceMapSemanticsRetainedBlockerProtocolRow.lean"
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

READINESS_REVIEW_TARGET = "review_qft_gr_source_map_semantics_protocol_row_readiness"
STRESS_ENERGY_DOMAIN_TARGET = (
    "derive_or_refute_qft_gr_stress_energy_operator_domain_semantics"
)
SURFACE_ID = "qft_gr_source_map_semantics_protocol_row_readiness_review_v0"
PROTOCOL_SURFACE_ID = "qft_gr_source_map_semantics_retained_blocker_protocol_row_v0"
RETAINED_BLOCKER = "PHASE1-BLOCKER-QFTGR-STRESS-ENERGY-EXPECTATION-SOURCE-MAP-RETAINED"
READINESS_EVIDENCE = str(READINESS_REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
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


def test_readiness_review_authorizes_only_stress_energy_operator_domain_slice() -> None:
    text = _read(READINESS_REVIEW_PATH)

    for token in {
        SURFACE_ID,
        READINESS_REVIEW_TARGET,
        STRESS_ENERGY_DOMAIN_TARGET,
        "authorize_bounded_stress_energy_operator_domain_semantics",
        "authorizeBoundedStressEnergyOperatorDomain",
        ".stressEnergyOperatorDomainDerivation",
        ".stressEnergyOperatorDomainDischarged",
        "qft_gr_source_map_semantics_readiness_review_authorizes_stress_energy_domain_v0",
        "qft_gr_source_map_semantics_readiness_review_selected_next_target_v0",
        "qft_gr_source_map_semantics_readiness_review_frontier_target_v0",
    }:
        assert token in text

    protocol_text = _read(PROTOCOL_ROW_PATH)
    assert PROTOCOL_SURFACE_ID in protocol_text
    assert "qftGRSourceMapSemanticsReadinessReviewTargetId" in protocol_text


def test_readiness_review_preserves_fail_closed_boundaries() -> None:
    text = _read(READINESS_REVIEW_PATH)

    for theorem in {
        "qft_gr_source_map_semantics_readiness_review_no_broader_theorem_work_v0",
        "qft_gr_source_map_semantics_readiness_review_expectation_functional_not_authorized_v0",
        "qft_gr_source_map_semantics_readiness_review_renormalized_expectation_not_authorized_v0",
        "qft_gr_source_map_semantics_readiness_review_weak_curvature_source_not_authorized_v0",
        "qft_gr_source_map_semantics_readiness_review_covariance_conservation_not_authorized_v0",
        "qft_gr_source_map_semantics_readiness_review_full_source_map_closure_not_authorized_v0",
        "qft_gr_source_map_semantics_readiness_review_no_seam_closure_v0",
        "qft_gr_source_map_semantics_readiness_review_no_semiclassical_gravity_claim_v0",
        "qft_gr_source_map_semantics_readiness_review_no_einstein_equation_claim_v0",
        "qft_gr_source_map_semantics_readiness_review_phase2_not_authorized_v0",
        "qft_gr_source_map_semantics_readiness_review_master_action_not_promoted_v0",
        "qft_gr_source_map_semantics_readiness_review_no_empirical_claim_v0",
        "qft_gr_source_map_semantics_readiness_review_governance_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_frontier_and_aggregate_point_to_stress_energy_domain_target() -> None:
    assert_frontier_matches_registry()
    aggregate_text = _read(AGGREGATE_PATH)
    frontier_text = _read(FRONTIER_PATH)

    assert (
        "import ToeFormal.Derivation.QFTGRSourceMapSemanticsProtocolRowReadinessReview"
        in aggregate_text
    )
    assert f'next_strict_slice :=\n        "{STRESS_ENERGY_DOMAIN_TARGET}"' in frontier_text
    assert f'def previousLiveNextStrictTargetV0 : String :=\n  "{READINESS_REVIEW_TARGET}"' in (
        frontier_text
    )
    assert f'def currentLiveNextStrictTargetV0 : String :=\n  "{STRESS_ENERGY_DOMAIN_TARGET}"' in (
        frontier_text
    )


def test_loop_registry_rotates_qft_gr_to_bounded_operator_domain_slice() -> None:
    assert_current_target_consistent()
    assert_forbidden_promotions_closed()
    payload = _registry()
    state = payload["current_target_state"]

    assert state["previous_live_next_target"] == READINESS_REVIEW_TARGET
    assert state["live_next_target"] == STRESS_ENERGY_DOMAIN_TARGET
    assert state["live_next_target_evidence"] == READINESS_EVIDENCE
    assert state["active_lane"] == "qft_gr_source_map"
    assert STRESS_ENERGY_DOMAIN_TARGET in payload["next_strict_target_coverage"]

    qft_gr = _workstream(payload, "qft_gr_source_map")
    assert qft_gr["status"] == "active"
    assert qft_gr["authorization_evidence"] == READINESS_EVIDENCE
    assert qft_gr["consumed_target"] == READINESS_REVIEW_TARGET
    assert qft_gr["prior_surface"] == PROTOCOL_SURFACE_ID
    assert qft_gr["latest_surface"] == SURFACE_ID
    assert qft_gr["authorized_next_strict_target"] == STRESS_ENERGY_DOMAIN_TARGET
    assert qft_gr["readiness_review_status"] == "completed"
    assert qft_gr["readiness_review_evidence"] == READINESS_EVIDENCE
    assert qft_gr["readiness_review_decision"] == (
        "authorize_bounded_stress_energy_operator_domain_semantics"
    )
    assert qft_gr["bounded_stress_energy_operator_domain_slice_authorized"] == "yes"
    assert qft_gr["stress_energy_operator_domain_obligation"] == "authorized_next_slice"
    assert qft_gr["stress_energy_operator_domain_semantics_status"] == "authorized_next_slice"
    assert qft_gr["qft_state_expectation_functional_semantics_authorized"] == "no"
    assert qft_gr["renormalized_expectation_semantics_authorized"] == "no"
    assert qft_gr["gr_weak_curvature_source_identification_semantics_authorized"] == "no"
    assert qft_gr["covariance_conservation_semantics_authorized"] == "no"
    assert qft_gr["full_source_map_semantic_closure_authorized"] == "no"
    assert qft_gr["theorem_work_authorized"] == (
        "bounded_stress_energy_operator_domain_semantics_only"
    )

    master_action = _workstream(payload, "master_action_dependency_frontier")
    assert master_action["status"] == "paused"
    assert master_action["latest_surface"] == SURFACE_ID
    assert master_action["authorization_evidence"] == READINESS_EVIDENCE
    assert master_action["authorized_next_strict_target"] == STRESS_ENERGY_DOMAIN_TARGET
    assert master_action["qft_gr_protocol_row_readiness_review_status"] == "completed"
    assert master_action["qft_gr_protocol_row_readiness_review_evidence"] == READINESS_EVIDENCE
    assert master_action["qft_gr_stress_energy_operator_domain_semantics_status"] == (
        "authorized_next_slice"
    )
    assert master_action["promotion_authorized"] == "no"

    edges = {(edge["from"], edge["to"]) for edge in payload["dependency_edges"]}
    assert (
        "qft_gr_source_map_semantics_retained_blocker_protocol_row",
        "qft_gr_source_map_semantics_protocol_row_readiness_review",
    ) in edges
    assert (
        "qft_gr_source_map_semantics_protocol_row_readiness_review",
        "qft_gr_stress_energy_operator_domain_semantics",
    ) in edges


def test_public_surfaces_and_manifest_boundary_are_synchronized() -> None:
    assert_public_surfaces_match_registry()
    for path in [README_PATH, STATE_PATH, ROADMAP_PATH, STRICT_MAP_PATH]:
        text = _read(path)
        assert "QFTGRSourceMapSemanticsProtocolRowReadinessReview.lean" in text
        assert STRESS_ENERGY_DOMAIN_TARGET in text
        assert RETAINED_BLOCKER in text

    for path in [SEAM_REGISTRY_PATH, SEAM_INVENTORY_PATH]:
        text = _read(path)
        assert "QFT_GR_SOURCE_MAP_SEMANTICS_READINESS_REVIEW" in text
        assert STRESS_ENERGY_DOMAIN_TARGET in text

    inventory_text = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-QFTGR-SOURCE-MAP-SEMANTICS-READINESS-REVIEW-v0" in inventory_text
    assert READINESS_EVIDENCE in inventory_text
    assert PROTOCOL_EVIDENCE in inventory_text
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_source_map_semantics_protocol_row_readiness_review_gate.py"
    )
