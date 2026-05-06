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
    skip_if_not_current_target,
    workstream,
)


REPO_ROOT = find_repo_root(Path(__file__))
SURFACE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_StateExpectationFunctionalSemantics.lean"
)
SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostRebaseNextBoundedAttackSelection.lean"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_STATE_EXPECTATION_FUNCTIONAL_SEMANTICS_BOUNDED_ATTACK_20260503_v0.json"
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

SURFACE_ID = "QFT_GR_STATE_EXPECTATION_FUNCTIONAL_SEMANTICS_v0"
PREVIOUS_TARGET = "prepare_qft_gr_state_expectation_functional_semantics_bounded_attack"
RESULT_REVIEW_TARGET = "review_qft_gr_state_expectation_functional_semantics_result"
RENORMALIZED_PREP_TARGET = "prepare_qft_gr_renormalized_expectation_value_semantics_bounded_attack"
RENORMALIZED_REVIEW_TARGET = "review_qft_gr_renormalized_expectation_value_semantics_result"
CURRENT_PREVIOUS_TARGET = "review_qft_gr_covariant_conservation_obligation_semantics_result"
LIVE_TARGET = "prepare_qft_gr_bianchi_compatibility_obligation_semantics_bounded_attack"
SELECTION_TARGET = "select_next_post_rebase_bounded_attack"
RESULT_TOKEN = "QFT_GR_STATE_EXPECTATION_FUNCTIONAL_SEMANTICS_SUPPLIED_ONLY"
FRESH_DELTA_ID = (
    "QFT_GR_STATE_EXPECTATION_FUNCTIONAL_PACKAGE_ONLY_COUNTEREXAMPLE_FRESH_DELTA_v0"
)
RETAINED_BLOCKER = (
    "PHASE1-BLOCKER-QFTGR-STATE-EXPECTATION-FUNCTIONAL-SEMANTICS-RETAINED"
)
REPORT_ID = "QFT_GR_STATE_EXPECTATION_FUNCTIONAL_SEMANTICS_BOUNDED_ATTACK_20260503_v0"
SURFACE_EVIDENCE = str(SURFACE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
SELECTION_EVIDENCE = str(SELECTION_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _registry() -> dict[str, Any]:
    return _json(REGISTRY_PATH)


def test_state_expectation_functional_surface_records_supplied_route_and_refutation() -> None:
    text = _read(SURFACE_PATH)

    for token in {
        SURFACE_ID,
        PREVIOUS_TARGET,
        RESULT_REVIEW_TARGET,
        RESULT_TOKEN,
        FRESH_DELTA_ID,
        RETAINED_BLOCKER,
        "QFTGRStateExpectationFunctionalSemanticPackage",
        "QFTGRStateExpectationFunctionalSemanticData",
        "stateExpectationFunctionalPackageOfSuppliedSemantics",
        "supplied_state_expectation_functional_semantics_constructs_package_v0",
        "qft_gr_source_map_package_does_not_force_state_expectation_functional_v0",
        "qft_gr_state_expectation_functional_semantics_supplied_route_available_v0",
        "qft_gr_state_expectation_functional_semantics_package_only_refuted_v0",
        "qft_gr_state_expectation_functional_semantics_retained_as_supplied_v0",
        "qft_gr_state_expectation_functional_semantics_result_token_v0",
        "qft_gr_state_expectation_functional_semantics_selected_next_target_v0",
    }:
        assert token in text


def test_state_expectation_functional_surface_preserves_fail_closed_boundaries() -> None:
    text = _read(SURFACE_PATH)

    for theorem in {
        "qft_gr_state_expectation_functional_semantics_renormalized_expectation_not_authorized_v0",
        "qft_gr_state_expectation_functional_semantics_hadamard_state_not_authorized_v0",
        "qft_gr_state_expectation_functional_semantics_self_adjointness_not_authorized_v0",
        "qft_gr_state_expectation_functional_semantics_domain_density_not_authorized_v0",
        "qft_gr_state_expectation_functional_semantics_weak_curvature_source_not_authorized_v0",
        "qft_gr_state_expectation_functional_semantics_covariance_conservation_not_authorized_v0",
        "qft_gr_state_expectation_functional_semantics_full_source_map_closure_not_authorized_v0",
        "qft_gr_state_expectation_functional_semantics_no_seam_closure_v0",
        "qft_gr_state_expectation_functional_semantics_no_semiclassical_gravity_claim_v0",
        "qft_gr_state_expectation_functional_semantics_no_einstein_equation_claim_v0",
        "qft_gr_state_expectation_functional_semantics_phase2_not_authorized_v0",
        "qft_gr_state_expectation_functional_semantics_master_action_not_promoted_v0",
        "qft_gr_state_expectation_functional_semantics_no_empirical_claim_v0",
        "qft_gr_state_expectation_functional_semantics_governance_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_state_expectation_functional_report_records_supplied_only_result() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["current_target"] == PREVIOUS_TARGET
    assert report["consumed_selection_target"] == SELECTION_TARGET
    assert report["selected_next_target"] == RESULT_REVIEW_TARGET
    assert report["result_token"] == RESULT_TOKEN
    assert report["fresh_delta_id"] == FRESH_DELTA_ID
    assert report["fresh_delta_kind"] == "counterexample"
    assert report["retained_blocker"] == RETAINED_BLOCKER
    assert report["supplied_route"]["status"] == "available"
    assert report["supplied_route"]["supplied_object"] == (
        "QFTGRStateExpectationFunctionalSemanticPackage"
    )
    assert report["refutation"]["status"] == "package_only_derivation_refuted"
    assert report["refutation"]["lean_theorem"] == (
        "qft_gr_source_map_package_does_not_force_state_expectation_functional_v0"
    )
    assert report["nonclaim_boundaries"] == {
        "renormalized_expectation_semantics_authorized": False,
        "hadamard_state_adequacy_authorized": False,
        "operator_self_adjointness_authorized": False,
        "domain_density_proof_authorized": False,
        "weak_curvature_source_identification_authorized": False,
        "covariance_conservation_authorized": False,
        "full_source_map_closure_authorized": False,
        "qft_gr_seam_closed": False,
        "semiclassical_gravity_claim": False,
        "einstein_equation_derivation_claim": False,
        "phase2_authorized": False,
        "master_action_promotion_authorized": False,
        "empirical_claim": False,
    }


def test_registry_rotates_to_state_expectation_functional_result_review() -> None:
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_forbidden_promotions_closed()
    assert_public_surfaces_match_registry()
    payload = _registry()
    skip_if_not_current_target(payload, LIVE_TARGET)
    state = payload["current_target_state"]

    assert state["previous_live_next_target"] == CURRENT_PREVIOUS_TARGET
    assert state["live_next_target"] == LIVE_TARGET
    assert state["active_lane"] == (
        "qft_gr_bianchi_compatibility_obligation_semantics_preparation"
    )
    assert "post_rebase_next_bounded_attack_selection" in state["paused_lanes"]

    selection = workstream("post_rebase_next_bounded_attack_selection", payload)
    assert selection["status"] == "paused"
    assert selection["authorized_next_strict_target"] == PREVIOUS_TARGET
    assert selection["selection_status"] == "completed"
    assert selection["state_expectation_functional_semantics_surface"] == SURFACE_EVIDENCE
    assert selection["state_expectation_functional_result_review_target"] == RESULT_REVIEW_TARGET

    qft_gr = workstream("qft_gr_source_map", payload)
    assert qft_gr["status"] == "paused"
    assert qft_gr["authorized_next_strict_target"] == LIVE_TARGET
    assert qft_gr["consumed_target"] == CURRENT_PREVIOUS_TARGET
    assert qft_gr["latest_surface"] == (
        "qft_gr_covariant_conservation_obligation_semantics_result_review_v0"
    )
    assert qft_gr["last_fresh_delta_kind"] == "counterexample"
    assert qft_gr["last_fresh_delta_id"] == (
        "QFT_GR_COVARIANT_CONSERVATION_OBLIGATION_SEMANTICS_COUNTEREXAMPLE_FRESH_DELTA_v0"
    )
    assert qft_gr["state_expectation_functional_semantics_status"] == (
        "completed_supplied_route_available_package_only_refuted"
    )
    assert qft_gr["state_expectation_functional_supplied_route_available"] == "yes"
    assert qft_gr["state_expectation_functional_package_only_refuted"] == "yes"
    assert qft_gr["state_expectation_functional_derived_from_source_map_package_alone"] == "no"
    assert qft_gr["state_expectation_functional_result_token"] == RESULT_TOKEN
    assert qft_gr["state_expectation_functional_result_review_target"] == RESULT_REVIEW_TARGET
    assert qft_gr["renormalized_expectation_semantics_authorized"] == "no"
    assert qft_gr["hadamard_state_adequacy_authorized"] == "no"
    assert qft_gr["operator_self_adjointness_authorized"] == "no"
    assert qft_gr["domain_density_proof_authorized"] == "no"
    assert qft_gr["full_source_map_semantic_closure_authorized"] == "no"

    active = workstream("qft_gr_state_expectation_functional_semantics_result_review", payload)
    assert active["status"] == "paused"
    assert active["authorized_next_strict_target"] == RENORMALIZED_PREP_TARGET
    assert active["state_expectation_functional_semantics_surface"] == SURFACE_EVIDENCE
    assert active["state_expectation_functional_semantics_report"] == REPORT_EVIDENCE
    assert active["result_token"] == RESULT_TOKEN
    assert active["fresh_delta_id"] == FRESH_DELTA_ID
    assert active["result_review_status"] == "completed"
    assert active["renormalized_expectation_semantics_authorized"] == "no"
    assert active["hadamard_state_adequacy_authorized"] == "no"
    assert active["operator_self_adjointness_authorized"] == "no"
    assert active["domain_density_proof_authorized"] == "no"
    assert active["weak_curvature_source_identification_authorized"] == "no"
    assert active["covariance_conservation_authorized"] == "no"
    assert active["full_source_map_closure_authorized"] == "no"
    assert active["qft_gr_seam_closed"] == "no"
    assert active["phase2_authorized"] == "no"
    assert active["master_action_promotion_authorized"] == "no"

    renormalized_prep = workstream(
        "qft_gr_renormalized_expectation_value_semantics_preparation", payload
    )
    assert renormalized_prep["status"] == "paused"
    assert renormalized_prep["authorized_next_strict_target"] == RENORMALIZED_REVIEW_TARGET
    assert renormalized_prep["consumed_target"] == RENORMALIZED_PREP_TARGET

    assert LIVE_TARGET in payload["next_strict_target_coverage"]
    assert RETAINED_BLOCKER in payload["retained_blocker_coverage"]
    edges = {(edge["from"], edge["to"]) for edge in payload["dependency_edges"]}
    assert (
        "post_rebase_next_bounded_attack_selection",
        "qft_gr_state_expectation_functional_semantics",
    ) in edges
    assert (
        "qft_gr_state_expectation_functional_semantics",
        "qft_gr_state_expectation_functional_semantics_result_review",
    ) in edges


def test_public_surfaces_and_inventory_track_state_expectation_functional_slice() -> None:
    for path in [README_PATH, STATE_PATH, ROADMAP_PATH, STRICT_MAP_PATH]:
        text = _read(path)
        assert LIVE_TARGET in text
        assert RESULT_REVIEW_TARGET in text
        assert PREVIOUS_TARGET in text
        assert "QFT_GR_StateExpectationFunctionalSemantics.lean" in text
        assert RESULT_TOKEN in text

    for path in [SEAM_REGISTRY_PATH, SEAM_INVENTORY_PATH]:
        text = _read(path)
        assert LIVE_TARGET in text
        assert SURFACE_ID in text
        assert RESULT_TOKEN in text
        assert REPORT_EVIDENCE in text

    inventory_text = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-QFTGR-STATE-EXPECTATION-FUNCTIONAL-SEMANTICS-v0" in inventory_text
    assert "QFT_GR_StateExpectationFunctionalSemantics.lean" in inventory_text
    assert LIVE_TARGET in inventory_text
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_state_expectation_functional_semantics_gate.py"
    )
