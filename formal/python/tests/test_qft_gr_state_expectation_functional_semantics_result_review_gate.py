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
    / "QFT_GR_StateExpectationFunctionalSemanticsResultReview.lean"
)
SOURCE_SURFACE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_StateExpectationFunctionalSemantics.lean"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_STATE_EXPECTATION_FUNCTIONAL_SEMANTICS_RESULT_REVIEW_20260503_v0.json"
)
SOURCE_REPORT_PATH = (
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

SURFACE_ID = "qft_gr_state_expectation_functional_semantics_result_review_v0"
PREVIOUS_TARGET = "review_qft_gr_state_expectation_functional_semantics_result"
SELECTED_NEXT_TARGET = "prepare_qft_gr_renormalized_expectation_value_semantics_bounded_attack"
RENORMALIZED_REVIEW_TARGET = "review_qft_gr_renormalized_expectation_value_semantics_result"
CURRENT_PREVIOUS_TARGET = "review_qft_gr_covariant_conservation_obligation_semantics_result"
LIVE_TARGET = "prepare_qft_gr_bianchi_compatibility_obligation_semantics_bounded_attack"
CURRENT_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_CovariantConservationObligationSemanticsResultReview.lean"
)
RESULT_TOKEN = "QFT_GR_STATE_EXPECTATION_FUNCTIONAL_SEMANTICS_SUPPLIED_ONLY"
REPORT_ID = "QFT_GR_STATE_EXPECTATION_FUNCTIONAL_SEMANTICS_RESULT_REVIEW_20260503_v0"
RETAINED_BLOCKER = (
    "PHASE1-BLOCKER-QFTGR-RENORMALIZED-EXPECTATION-VALUE-SEMANTICS-RETAINED"
)
SOURCE_RETAINED_BLOCKER = (
    "PHASE1-BLOCKER-QFTGR-STATE-EXPECTATION-FUNCTIONAL-SEMANTICS-RETAINED"
)
SURFACE_EVIDENCE = str(SURFACE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
SOURCE_SURFACE_EVIDENCE = str(SOURCE_SURFACE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
SOURCE_REPORT_EVIDENCE = str(SOURCE_REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _registry() -> dict[str, Any]:
    return _json(REGISTRY_PATH)


def test_state_expectation_functional_result_review_surface_consumes_result() -> None:
    text = _read(SURFACE_PATH)

    for token in {
        SURFACE_ID,
        PREVIOUS_TARGET,
        SELECTED_NEXT_TARGET,
        RESULT_TOKEN,
        "QFTGRStateExpectationFunctionalResultReviewStatus",
        "QFTGRStateExpectationFunctionalResultReviewDecision",
        "acceptSuppliedOnlyAndPrepareRenormalizedExpectationValueSemantics",
        "qft_gr_state_expectation_functional_result_review_consumes_live_target_v0",
        "qft_gr_state_expectation_functional_result_review_completed_v0",
        "qft_gr_state_expectation_functional_result_review_accepts_supplied_only_v0",
        "qft_gr_state_expectation_functional_result_review_package_only_refuted_v0",
        "qft_gr_state_expectation_functional_result_review_retained_as_supplied_v0",
        "qft_gr_state_expectation_functional_result_review_selected_decision_v0",
        "qft_gr_state_expectation_functional_result_review_selected_next_target_v0",
    }:
        assert token in text


def test_state_expectation_functional_result_review_preserves_fail_closed_boundaries() -> None:
    text = _read(SURFACE_PATH)

    for theorem in {
        "qft_gr_state_expectation_functional_result_review_source_map_package_only_not_authorized_v0",
        "qft_gr_state_expectation_functional_result_review_renormalized_expectation_not_authorized_v0",
        "qft_gr_state_expectation_functional_result_review_hadamard_state_not_authorized_v0",
        "qft_gr_state_expectation_functional_result_review_self_adjointness_not_authorized_v0",
        "qft_gr_state_expectation_functional_result_review_domain_density_not_authorized_v0",
        "qft_gr_state_expectation_functional_result_review_weak_curvature_source_not_authorized_v0",
        "qft_gr_state_expectation_functional_result_review_covariance_conservation_not_authorized_v0",
        "qft_gr_state_expectation_functional_result_review_full_source_map_closure_not_authorized_v0",
        "qft_gr_state_expectation_functional_result_review_no_seam_closure_v0",
        "qft_gr_state_expectation_functional_result_review_no_semiclassical_gravity_claim_v0",
        "qft_gr_state_expectation_functional_result_review_no_einstein_equation_claim_v0",
        "qft_gr_state_expectation_functional_result_review_phase2_not_authorized_v0",
        "qft_gr_state_expectation_functional_result_review_master_action_not_promoted_v0",
        "qft_gr_state_expectation_functional_result_review_no_empirical_claim_v0",
        "qft_gr_state_expectation_functional_result_review_governance_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_state_expectation_functional_result_review_report_records_selection() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["current_target"] == PREVIOUS_TARGET
    assert report["consumed_result_token"] == RESULT_TOKEN
    assert report["review_surface"] == SURFACE_EVIDENCE
    assert report["source_surface"] == SOURCE_SURFACE_EVIDENCE
    assert report["source_report"] == SOURCE_REPORT_EVIDENCE
    assert report["selected_next_target"] == SELECTED_NEXT_TARGET
    assert report["selected_decision"] == (
        "accept_supplied_only_and_prepare_renormalized_expectation_value_semantics"
    )
    assert report["review_result"] == "supplied_only_expectation_functional_result_consumed"
    assert report["accepted_result"]["supplied_object"] == (
        "QFTGRStateExpectationFunctionalSemanticPackage"
    )
    assert report["refutation_confirmed"]["status"] == (
        "source_map_package_only_derivation_refuted"
    )

    assert report["nonclaim_boundaries"] == {
        "source_map_package_only_derivation_authorized": False,
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
        "governance_manifest_enrollment_authorized": False,
    }


def test_registry_rotates_to_renormalized_expectation_value_preparation() -> None:
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_forbidden_promotions_closed()
    assert_public_surfaces_match_registry()
    payload = _registry()
    skip_if_not_current_target(payload, LIVE_TARGET)
    state = payload["current_target_state"]

    assert state["previous_live_next_target"] == CURRENT_PREVIOUS_TARGET
    assert state["live_next_target"] == LIVE_TARGET
    assert state["live_next_target_evidence"] == CURRENT_EVIDENCE
    assert state["active_lane"] == (
        "qft_gr_bianchi_compatibility_obligation_semantics_preparation"
    )
    assert "qft_gr_state_expectation_functional_semantics_result_review" in (
        state["paused_lanes"]
    )

    review = workstream("qft_gr_state_expectation_functional_semantics_result_review", payload)
    assert review["status"] == "paused"
    assert review["authorized_next_strict_target"] == SELECTED_NEXT_TARGET
    assert review["consumed_target"] == PREVIOUS_TARGET
    assert review["latest_surface"] == SURFACE_ID
    assert review["result_review_surface"] == SURFACE_EVIDENCE
    assert review["result_review_report"] == REPORT_EVIDENCE
    assert review["result_review_status"] == "completed"
    assert review["review_result"] == "supplied_only_expectation_functional_result_consumed"
    assert review["review_decision"] == (
        "accept_supplied_only_and_prepare_renormalized_expectation_value_semantics"
    )

    active = workstream(
        "qft_gr_renormalized_expectation_value_semantics_preparation", payload
    )
    assert active["status"] == "paused"
    assert active["retained_blocker"] == RETAINED_BLOCKER
    assert active["authorized_next_strict_target"] == RENORMALIZED_REVIEW_TARGET
    assert active["consumed_target"] == SELECTED_NEXT_TARGET
    assert active["authorization_evidence"] == (
        "formal/toe_formal/ToeFormal/Bridges/"
        "QFT_GR_RenormalizedExpectationValueSemantics.lean"
    )
    assert active["state_expectation_functional_result_review_surface"] == SURFACE_EVIDENCE
    assert active["state_expectation_functional_result_review_report"] == REPORT_EVIDENCE
    assert active["preparation_scope"] == "renormalized_expectation_value_semantics_slot_only"
    assert active["renormalized_expectation_value_semantics_status"] == (
        "QFT_GR_RENORMALIZED_EXPECTATION_VALUE_SEMANTICS_SUPPLIED_ONLY"
    )
    assert active["full_source_map_closure_authorized"] == "no"
    assert active["qft_gr_seam_closed"] == "no"
    assert active["phase2_authorized"] == "no"
    assert active["master_action_promotion_authorized"] == "no"

    qft_gr = workstream("qft_gr_source_map", payload)
    assert qft_gr["state_expectation_functional_result_review_status"] == "completed"
    assert qft_gr["state_expectation_functional_result_review_status"] == "completed"
    assert qft_gr["state_expectation_functional_result_review_evidence"] == SURFACE_EVIDENCE
    assert qft_gr["renormalized_expectation_value_semantics_status"] == (
        "QFT_GR_RENORMALIZED_EXPECTATION_VALUE_SEMANTICS_SUPPLIED_ONLY"
    )

    assert LIVE_TARGET in payload["next_strict_target_coverage"]
    assert SELECTED_NEXT_TARGET in payload["next_strict_target_coverage"]
    assert RETAINED_BLOCKER in payload["retained_blocker_coverage"]
    assert SOURCE_RETAINED_BLOCKER in payload["retained_blocker_coverage"]
    edges = {(edge["from"], edge["to"]) for edge in payload["dependency_edges"]}
    assert (
        "qft_gr_state_expectation_functional_semantics_result_review",
        "qft_gr_renormalized_expectation_value_semantics_preparation",
    ) in edges


def test_public_surfaces_track_result_review_and_next_preparation() -> None:
    for path in [README_PATH, STATE_PATH, ROADMAP_PATH, STRICT_MAP_PATH]:
        text = _read(path)
        assert LIVE_TARGET in text
        assert PREVIOUS_TARGET in text
        assert "QFT_GR_StateExpectationFunctionalSemanticsResultReview.lean" in text
        assert RESULT_TOKEN in text

    for path in [SEAM_REGISTRY_PATH, SEAM_INVENTORY_PATH]:
        text = _read(path)
        assert LIVE_TARGET in text
        assert SURFACE_ID in text
        assert REPORT_EVIDENCE in text

    inventory_text = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-QFTGR-STATE-EXPECTATION-FUNCTIONAL-RESULT-REVIEW-v0" in inventory_text
    assert SURFACE_EVIDENCE in inventory_text
    assert REPORT_EVIDENCE in inventory_text
    assert LIVE_TARGET in inventory_text

    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_state_expectation_functional_semantics_result_review_gate.py"
    )
