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
    / "QFT_GR_RenormalizedExpectationValueSemantics.lean"
)
SOURCE_SURFACE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_StateExpectationFunctionalSemanticsResultReview.lean"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_RENORMALIZED_EXPECTATION_VALUE_SEMANTICS_BOUNDED_ATTACK_20260503_v0.json"
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

SURFACE_ID = "QFT_GR_RENORMALIZED_EXPECTATION_VALUE_SEMANTICS_v0"
PREVIOUS_TARGET = "prepare_qft_gr_renormalized_expectation_value_semantics_bounded_attack"
SELECTED_NEXT_TARGET = "review_qft_gr_renormalized_expectation_value_semantics_result"
CLASSICAL_SOURCE_PREPARATION_TARGET = (
    "prepare_qft_gr_classical_source_admissibility_semantics_bounded_attack"
)
CURRENT_PREVIOUS_TARGET = "review_qft_gr_covariant_conservation_obligation_semantics_result"
LIVE_TARGET = "prepare_qft_gr_bianchi_compatibility_obligation_semantics_bounded_attack"
CURRENT_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_CovariantConservationObligationSemanticsResultReview.lean"
)
RESULT_TOKEN = "QFT_GR_RENORMALIZED_EXPECTATION_VALUE_SEMANTICS_SUPPLIED_ONLY"
REPORT_ID = "QFT_GR_RENORMALIZED_EXPECTATION_VALUE_SEMANTICS_BOUNDED_ATTACK_20260503_v0"
RETAINED_BLOCKER = (
    "PHASE1-BLOCKER-QFTGR-RENORMALIZED-EXPECTATION-VALUE-SEMANTICS-RETAINED"
)
FRESH_DELTA_ID = (
    "QFT_GR_RENORMALIZED_EXPECTATION_VALUE_PACKAGE_ONLY_COUNTEREXAMPLE_FRESH_DELTA_v0"
)
SURFACE_EVIDENCE = str(SURFACE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
SOURCE_SURFACE_EVIDENCE = str(SOURCE_SURFACE_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _registry() -> dict[str, Any]:
    return _json(REGISTRY_PATH)


def test_renormalized_expectation_value_semantics_surface_records_supplied_slot() -> None:
    text = _read(SURFACE_PATH)

    for token in {
        SURFACE_ID,
        PREVIOUS_TARGET,
        SELECTED_NEXT_TARGET,
        RESULT_TOKEN,
        "QFTGRRenormalizedExpectationValueSemanticPackage",
        "QFTGRRenormalizedExpectationValueSemanticData",
        "supplied_renormalized_expectation_value_semantics_constructs_package_v0",
        "qft_gr_state_expectation_functional_semantics_does_not_force_renormalized_expectation_value_v0",
        "qft_gr_renormalized_expectation_value_semantics_consumes_live_target_v0",
        "qft_gr_renormalized_expectation_value_semantics_supplied_route_available_v0",
        "qft_gr_renormalized_expectation_value_semantics_state_expectation_only_refuted_v0",
        "qft_gr_renormalized_expectation_value_semantics_retained_as_supplied_v0",
        "qft_gr_renormalized_expectation_value_semantics_result_token_v0",
        "qft_gr_renormalized_expectation_value_semantics_selected_next_target_v0",
    }:
        assert token in text


def test_renormalized_expectation_value_semantics_preserves_fail_closed_boundaries() -> None:
    text = _read(SURFACE_PATH)

    for theorem in {
        "qft_gr_renormalized_expectation_value_semantics_scheme_validity_not_authorized_v0",
        "qft_gr_renormalized_expectation_value_semantics_hadamard_state_not_authorized_v0",
        "qft_gr_renormalized_expectation_value_semantics_finite_stress_energy_tensor_not_authorized_v0",
        "qft_gr_renormalized_expectation_value_semantics_self_adjointness_not_authorized_v0",
        "qft_gr_renormalized_expectation_value_semantics_domain_density_not_authorized_v0",
        "qft_gr_renormalized_expectation_value_semantics_covariant_conservation_not_authorized_v0",
        "qft_gr_renorm_expectation_value_classical_source_not_authorized_v0",
        "qft_gr_renormalized_expectation_value_semantics_weak_curvature_source_not_authorized_v0",
        "qft_gr_renorm_expectation_value_semiclassical_einstein_not_authorized_v0",
        "qft_gr_renormalized_expectation_value_semantics_full_source_map_closure_not_authorized_v0",
        "qft_gr_renormalized_expectation_value_semantics_no_seam_closure_v0",
        "qft_gr_renormalized_expectation_value_semantics_no_semiclassical_gravity_claim_v0",
        "qft_gr_renormalized_expectation_value_semantics_no_einstein_equation_claim_v0",
        "qft_gr_renormalized_expectation_value_semantics_phase2_not_authorized_v0",
        "qft_gr_renormalized_expectation_value_semantics_master_action_not_promoted_v0",
        "qft_gr_renormalized_expectation_value_semantics_no_empirical_claim_v0",
        "qft_gr_renormalized_expectation_value_semantics_governance_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_renormalized_expectation_value_semantics_report_records_nonclaim_result() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["current_target"] == PREVIOUS_TARGET
    assert report["selected_next_target"] == SELECTED_NEXT_TARGET
    assert report["surface"] == SURFACE_EVIDENCE
    assert report["source_surface"] == SOURCE_SURFACE_EVIDENCE
    assert report["result_token"] == RESULT_TOKEN
    assert report["fresh_delta_id"] == FRESH_DELTA_ID
    assert report["fresh_delta_kind"] == "counterexample"
    assert report["retained_blocker"] == RETAINED_BLOCKER
    assert report["supplied_route"]["supplied_object"] == (
        "QFTGRRenormalizedExpectationValueSemanticPackage"
    )
    assert report["refutation"]["status"] == (
        "state_expectation_functional_only_derivation_refuted"
    )
    assert not any(report["nonclaim_boundaries"].values())


def test_registry_retains_renormalized_expectation_value_semantics_history() -> None:
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
    assert "qft_gr_renormalized_expectation_value_semantics_preparation" in (
        state["paused_lanes"]
    )
    assert "qft_gr_renormalized_expectation_value_semantics_result_review" in (
        state["paused_lanes"]
    )

    prep = workstream("qft_gr_renormalized_expectation_value_semantics_preparation", payload)
    assert prep["status"] == "paused"
    assert prep["authorized_next_strict_target"] == SELECTED_NEXT_TARGET
    assert prep["consumed_target"] == PREVIOUS_TARGET
    assert prep["latest_surface"] == SURFACE_ID
    assert prep["renormalized_expectation_value_semantics_result_token"] == RESULT_TOKEN
    assert prep["result_review_status"] == "prepared_for_live_result_review"

    review = workstream(
        "qft_gr_renormalized_expectation_value_semantics_result_review", payload
    )
    assert review["status"] == "paused"
    assert review["authorized_next_strict_target"] == CLASSICAL_SOURCE_PREPARATION_TARGET
    assert review["consumed_target"] == SELECTED_NEXT_TARGET
    assert review["renormalized_expectation_value_semantics_surface"] == SURFACE_EVIDENCE
    assert review["renormalized_expectation_value_semantics_report"] == REPORT_EVIDENCE
    assert review["result_token"] == RESULT_TOKEN
    assert review["fresh_delta_id"] == FRESH_DELTA_ID
    assert review["supplied_route_available"] == "yes"
    assert review["state_expectation_functional_only_derivation_refuted"] == "yes"
    assert review["full_source_map_closure_authorized"] == "no"
    assert review["qft_gr_seam_closed"] == "no"
    assert review["phase2_authorized"] == "no"
    assert review["master_action_promotion_authorized"] == "no"

    qft_gr = workstream("qft_gr_source_map", payload)
    assert qft_gr["renormalized_expectation_value_semantics_status"] == RESULT_TOKEN
    assert qft_gr["renormalized_expectation_value_semantics_status"] == RESULT_TOKEN
    assert qft_gr["renormalized_expectation_value_semantics_result_review_target"] == (
        SELECTED_NEXT_TARGET
    )

    assert CLASSICAL_SOURCE_PREPARATION_TARGET in payload["next_strict_target_coverage"]
    assert LIVE_TARGET in payload["next_strict_target_coverage"]
    assert SELECTED_NEXT_TARGET in payload["next_strict_target_coverage"]
    edges = {(edge["from"], edge["to"]) for edge in payload["dependency_edges"]}
    assert (
        "qft_gr_renormalized_expectation_value_semantics_preparation",
        "qft_gr_renormalized_expectation_value_semantics_result_review",
    ) in edges


def test_public_surfaces_track_renormalized_expectation_value_result_review() -> None:
    for path in [README_PATH, STATE_PATH, ROADMAP_PATH, STRICT_MAP_PATH]:
        text = _read(path)
        assert LIVE_TARGET in text
        assert CLASSICAL_SOURCE_PREPARATION_TARGET in text
        assert PREVIOUS_TARGET in text
        assert "QFT_GR_RenormalizedExpectationValueSemantics.lean" in text
        assert RESULT_TOKEN in text

    for path in [SEAM_REGISTRY_PATH, SEAM_INVENTORY_PATH]:
        text = _read(path)
        assert CLASSICAL_SOURCE_PREPARATION_TARGET in text
        assert LIVE_TARGET in text
        assert SURFACE_ID in text
        assert REPORT_EVIDENCE in text

    inventory_text = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-QFTGR-RENORMALIZED-EXPECTATION-VALUE-SEMANTICS-v0" in inventory_text
    assert SURFACE_EVIDENCE in inventory_text
    assert REPORT_EVIDENCE in inventory_text
    assert CLASSICAL_SOURCE_PREPARATION_TARGET in inventory_text

    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_renormalized_expectation_value_semantics_gate.py"
    )
