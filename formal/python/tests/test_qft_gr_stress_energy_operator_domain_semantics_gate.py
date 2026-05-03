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
    workstream,
)


REPO_ROOT = find_repo_root(Path(__file__))
OPERATOR_DOMAIN_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_StressEnergyOperatorDomainSemantics.lean"
)
READINESS_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRSourceMapSemanticsProtocolRowReadinessReview.lean"
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

SOURCE_TARGET = "derive_or_refute_qft_gr_stress_energy_operator_domain_semantics"
RESULT_REVIEW_TARGET = "review_qft_gr_stress_energy_operator_domain_semantics_result"
SURFACE_ID = "QFT_GR_STRESS_ENERGY_OPERATOR_DOMAIN_SEMANTICS_v0"
FRESH_DELTA_ID = (
    "QFT_GR_STRESS_ENERGY_OPERATOR_DOMAIN_PACKAGE_ONLY_COUNTEREXAMPLE_FRESH_DELTA_v0"
)
RETAINED_BLOCKER = (
    "PHASE1-BLOCKER-QFTGR-STRESS-ENERGY-OPERATOR-DOMAIN-SEMANTICS-RETAINED"
)
OPERATOR_DOMAIN_EVIDENCE = str(OPERATOR_DOMAIN_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
READINESS_EVIDENCE = str(READINESS_REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _registry() -> dict[str, Any]:
    return json.loads(_read(REGISTRY_PATH))


def _workstream(payload: dict[str, Any], workstream_id: str) -> dict[str, Any]:
    for item in payload["workstreams"]:
        if item["workstream_id"] == workstream_id:
            return item
    raise AssertionError(f"Missing workstream: {workstream_id}")


def test_operator_domain_semantics_surface_records_route_and_counterexample() -> None:
    text = _read(OPERATOR_DOMAIN_PATH)

    for token in {
        SURFACE_ID,
        SOURCE_TARGET,
        RESULT_REVIEW_TARGET,
        RETAINED_BLOCKER,
        FRESH_DELTA_ID,
        "counterexample",
        "QFTGRStressEnergyOperatorDomainSemanticData",
        "stressEnergyObjectOfOperatorDomainSemantics",
        "supplied_operator_domain_semantics_constructs_stress_energy_object_v0",
        "qft_gr_source_map_package_does_not_force_stress_energy_operator_domain_v0",
        "qft_gr_stress_energy_operator_domain_supplied_route_available_v0",
        "qft_gr_stress_energy_operator_domain_package_only_refuted_v0",
        "qft_gr_stress_energy_operator_domain_not_package_only_v0",
        "qft_gr_stress_energy_operator_domain_retained_as_supplied_v0",
        "qft_gr_stress_energy_operator_domain_selected_next_target_v0",
        "qft_gr_stress_energy_operator_domain_frontier_target_v0",
    }:
        assert token in text


def test_operator_domain_slice_preserves_fail_closed_boundaries() -> None:
    text = _read(OPERATOR_DOMAIN_PATH)

    for theorem in {
        "qft_gr_stress_energy_operator_domain_expectation_functional_not_authorized_v0",
        "qft_gr_stress_energy_operator_domain_renormalized_expectation_not_authorized_v0",
        "qft_gr_stress_energy_operator_domain_weak_curvature_source_not_authorized_v0",
        "qft_gr_stress_energy_operator_domain_covariance_conservation_not_authorized_v0",
        "qft_gr_stress_energy_operator_domain_full_source_map_closure_not_authorized_v0",
        "qft_gr_stress_energy_operator_domain_no_seam_closure_v0",
        "qft_gr_stress_energy_operator_domain_no_semiclassical_gravity_claim_v0",
        "qft_gr_stress_energy_operator_domain_no_einstein_equation_claim_v0",
        "qft_gr_stress_energy_operator_domain_phase2_not_authorized_v0",
        "qft_gr_stress_energy_operator_domain_master_action_not_promoted_v0",
        "qft_gr_stress_energy_operator_domain_no_empirical_claim_v0",
        "qft_gr_stress_energy_operator_domain_governance_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_frontier_and_aggregate_rotate_to_operator_domain_result_review() -> None:
    assert_frontier_matches_registry()
    aggregate_text = _read(AGGREGATE_PATH)
    frontier_text = _read(FRONTIER_PATH)

    assert (
        "import ToeFormal.Bridges.QFT_GR_StressEnergyOperatorDomainSemantics"
        in aggregate_text
    )
    assert "stress-energy operator-domain semantics slice" in frontier_text
    assert f'def previousLiveNextStrictTargetV0 : String :=\n  "{SOURCE_TARGET}"' in (
        frontier_text
    )
    assert f'def currentLiveNextStrictTargetV0 : String :=\n  "{RESULT_REVIEW_TARGET}"' in (
        frontier_text
    )


def test_loop_registry_tracks_operator_domain_result_review_only() -> None:
    assert_current_target_consistent()
    assert_forbidden_promotions_closed()
    payload = _registry()
    state = payload["current_target_state"]

    assert state["previous_live_next_target"] == SOURCE_TARGET
    assert state["live_next_target"] == RESULT_REVIEW_TARGET
    assert state["live_next_target_evidence"] == OPERATOR_DOMAIN_EVIDENCE
    assert state["active_lane"] == "qft_gr_source_map"
    assert RESULT_REVIEW_TARGET in payload["next_strict_target_coverage"]
    assert RETAINED_BLOCKER in payload["retained_blocker_coverage"]

    qft_gr = workstream("qft_gr_source_map", payload)
    assert qft_gr["status"] == "active"
    assert qft_gr["retained_blocker"] == RETAINED_BLOCKER
    assert qft_gr["authorization_evidence"] == OPERATOR_DOMAIN_EVIDENCE
    assert qft_gr["consumed_target"] == SOURCE_TARGET
    assert qft_gr["prior_surface"] == "qft_gr_source_map_semantics_protocol_row_readiness_review_v0"
    assert qft_gr["latest_surface"] == SURFACE_ID
    assert qft_gr["authorized_next_strict_target"] == RESULT_REVIEW_TARGET
    assert qft_gr["last_fresh_delta_kind"] == "counterexample"
    assert qft_gr["last_fresh_delta_id"] == FRESH_DELTA_ID
    assert qft_gr["last_fresh_delta_evidence"] == OPERATOR_DOMAIN_EVIDENCE
    assert qft_gr["stress_energy_operator_domain_semantics_status"] == (
        "completed_supplied_route_available_package_only_refuted"
    )
    assert qft_gr["stress_energy_operator_domain_obligation"] == (
        "retained_as_supplied_semantics_not_package_derived"
    )
    assert qft_gr["stress_energy_operator_domain_supplied_route_available"] == "yes"
    assert qft_gr["stress_energy_operator_domain_package_only_refuted"] == "yes"
    assert qft_gr["stress_energy_operator_domain_derived_from_source_map_package_alone"] == "no"
    assert qft_gr["bounded_stress_energy_operator_domain_slice_authorized"] == "completed"
    assert qft_gr["stress_energy_operator_domain_result_review_status"] == "pending"
    assert qft_gr["stress_energy_operator_domain_result_review_target"] == RESULT_REVIEW_TARGET
    assert qft_gr["qft_state_expectation_functional_semantics_authorized"] == "no"
    assert qft_gr["renormalized_expectation_semantics_authorized"] == "no"
    assert qft_gr["gr_weak_curvature_source_identification_semantics_authorized"] == "no"
    assert qft_gr["covariance_conservation_semantics_authorized"] == "no"
    assert qft_gr["full_source_map_semantic_closure_authorized"] == "no"
    assert qft_gr["theorem_work_authorized"] == "result_review_only_after_operator_domain_slice"

    master_action = _workstream(payload, "master_action_dependency_frontier")
    assert master_action["status"] == "paused"
    assert master_action["latest_surface"] == SURFACE_ID
    assert master_action["authorization_evidence"] == OPERATOR_DOMAIN_EVIDENCE
    assert master_action["authorized_next_strict_target"] == RESULT_REVIEW_TARGET
    assert master_action["qft_gr_protocol_row_readiness_review_status"] == "completed"
    assert master_action["qft_gr_protocol_row_readiness_review_evidence"] == READINESS_EVIDENCE
    assert master_action["qft_gr_stress_energy_operator_domain_semantics_status"] == (
        "completed_supplied_route_available_package_only_refuted"
    )
    assert (
        master_action["qft_gr_stress_energy_operator_domain_semantics_evidence"]
        == OPERATOR_DOMAIN_EVIDENCE
    )
    assert master_action["qft_gr_stress_energy_operator_domain_result_review_status"] == (
        "pending"
    )
    assert master_action["promotion_authorized"] == "no"

    edges = {(edge["from"], edge["to"]) for edge in payload["dependency_edges"]}
    assert (
        "qft_gr_source_map_semantics_protocol_row_readiness_review",
        "qft_gr_stress_energy_operator_domain_semantics",
    ) in edges
    assert (
        "qft_gr_stress_energy_operator_domain_semantics",
        "qft_gr_stress_energy_operator_domain_semantics_result_review",
    ) in edges


def test_public_surfaces_and_manifest_boundary_are_synchronized() -> None:
    assert_public_surfaces_match_registry()
    for path in [README_PATH, STATE_PATH, ROADMAP_PATH, STRICT_MAP_PATH]:
        text = _read(path)
        assert "QFT_GR_StressEnergyOperatorDomainSemantics.lean" in text
        assert RESULT_REVIEW_TARGET in text
        assert "package-only" in text or "PACKAGE_ONLY" in text

    for path in [SEAM_REGISTRY_PATH, SEAM_INVENTORY_PATH]:
        text = _read(path)
        assert "QFT_GR_STRESS_ENERGY_OPERATOR_DOMAIN_SEMANTICS_v0" in text
        assert RESULT_REVIEW_TARGET in text

    inventory_text = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-QFTGR-STRESS-ENERGY-OPERATOR-DOMAIN-SEMANTICS-v0" in inventory_text
    assert OPERATOR_DOMAIN_EVIDENCE in inventory_text
    assert READINESS_EVIDENCE in inventory_text
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_stress_energy_operator_domain_semantics_gate.py"
    )
