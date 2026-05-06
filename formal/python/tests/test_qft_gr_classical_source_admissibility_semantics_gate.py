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
    / "QFT_GR_ClassicalSourceAdmissibilitySemantics.lean"
)
SOURCE_SURFACE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_RenormalizedExpectationValueSemanticsResultReview.lean"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_CLASSICAL_SOURCE_ADMISSIBILITY_SEMANTICS_BOUNDED_ATTACK_20260503_v0.json"
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
CURRENT_EVIDENCE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_CovariantConservationObligationSemanticsResultReview.lean"
)

SURFACE_ID = "QFT_GR_CLASSICAL_SOURCE_ADMISSIBILITY_SEMANTICS_v0"
PREVIOUS_TARGET = "prepare_qft_gr_classical_source_admissibility_semantics_bounded_attack"
SOURCE_REVIEW_TARGET = "review_qft_gr_renormalized_expectation_value_semantics_result"
SOURCE_NEXT_TARGET = "review_qft_gr_classical_source_admissibility_semantics_result"
LIVE_TARGET = "prepare_qft_gr_bianchi_compatibility_obligation_semantics_bounded_attack"
CURRENT_RESULT_TOKEN = (
    "QFT_GR_COVARIANT_CONSERVATION_OBLIGATION_SEMANTICS_RESULT_REVIEW_CONSUMED_SUPPLIED_ONLY"
)
RESULT_TOKEN = "QFT_GR_CLASSICAL_SOURCE_ADMISSIBILITY_SEMANTICS_SUPPLIED_ONLY"
REPORT_ID = "QFT_GR_CLASSICAL_SOURCE_ADMISSIBILITY_SEMANTICS_BOUNDED_ATTACK_20260503_v0"
RETAINED_BLOCKER = (
    "PHASE1-BLOCKER-QFTGR-CLASSICAL-SOURCE-ADMISSIBILITY-SEMANTICS-RETAINED"
)
FRESH_DELTA_ID = (
    "QFT_GR_CLASSICAL_SOURCE_ADMISSIBILITY_SEMANTICS_COUNTEREXAMPLE_FRESH_DELTA_v0"
)
SOURCE_RESULT_TOKEN = (
    "QFT_GR_RENORMALIZED_EXPECTATION_VALUE_SEMANTICS_RESULT_REVIEW_CONSUMED_SUPPLIED_ONLY"
)
SURFACE_EVIDENCE = str(SURFACE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
SOURCE_SURFACE_EVIDENCE = str(SOURCE_SURFACE_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
CURRENT_EVIDENCE = str(CURRENT_EVIDENCE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _registry() -> dict[str, Any]:
    return _json(REGISTRY_PATH)


def test_classical_source_admissibility_surface_records_supplied_interface() -> None:
    text = _read(SURFACE_PATH)

    for token in {
        SURFACE_ID,
        PREVIOUS_TARGET,
        SOURCE_NEXT_TARGET,
        RESULT_TOKEN,
        "QFTGRClassicalSourceAdmissibilitySemanticPackage",
        "QFTGRClassicalSourceAdmissibilitySemanticData",
        "supplied_classical_source_admissibility_semantics_constructs_package_v0",
        "qft_gr_renormalized_expectation_value_semantics_does_not_force_classical_source_admissibility_v0",
        "qft_gr_classical_source_admissibility_semantics_consumes_live_target_v0",
        "qft_gr_classical_source_admissibility_semantics_supplied_route_available_v0",
        "qft_gr_classical_source_admissibility_semantics_renormalized_only_refuted_v0",
        "qft_gr_classical_source_admissibility_semantics_retained_as_supplied_v0",
        "qft_gr_classical_source_admissibility_semantics_result_token_v0",
        "qft_gr_classical_source_admissibility_semantics_selected_next_target_v0",
    }:
        assert token in text


def test_classical_source_admissibility_surface_preserves_boundaries() -> None:
    text = _read(SURFACE_PATH)

    for theorem in {
        "qft_gr_classical_source_admissibility_semantics_scheme_not_authorized_v0",
        "qft_gr_classical_source_admissibility_semantics_finite_tensor_not_authorized_v0",
        "qft_gr_classical_source_admissibility_semantics_hadamard_not_authorized_v0",
        "qft_gr_classical_source_admissibility_semantics_self_adjoint_not_authorized_v0",
        "qft_gr_classical_source_admissibility_semantics_domain_density_not_authorized_v0",
        "qft_gr_classical_source_admissibility_semantics_conservation_not_authorized_v0",
        "qft_gr_classical_source_admissibility_semantics_bianchi_source_not_authorized_v0",
        "qft_gr_classical_source_admissibility_semantics_einstein_coupling_not_authorized_v0",
        "qft_gr_classical_source_admissibility_semantics_weak_source_not_authorized_v0",
        "qft_gr_classical_source_admissibility_semantics_poisson_limit_not_authorized_v0",
        "qft_gr_classical_source_admissibility_semantics_semiclassical_eq_not_authorized_v0",
        "qft_gr_classical_source_admissibility_semantics_source_map_not_authorized_v0",
        "qft_gr_classical_source_admissibility_semantics_no_seam_closure_v0",
        "qft_gr_classical_source_admissibility_semantics_no_semiclassical_gravity_claim_v0",
        "qft_gr_classical_source_admissibility_semantics_no_einstein_claim_v0",
        "qft_gr_classical_source_admissibility_semantics_phase2_not_authorized_v0",
        "qft_gr_classical_source_admissibility_semantics_master_action_not_promoted_v0",
        "qft_gr_classical_source_admissibility_semantics_no_empirical_claim_v0",
        "qft_gr_classical_source_admissibility_semantics_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_classical_source_admissibility_report_records_nonclaim_result() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["current_target"] == PREVIOUS_TARGET
    assert report["consumed_result_review_target"] == SOURCE_REVIEW_TARGET
    assert report["consumed_result_token"] == SOURCE_RESULT_TOKEN
    assert report["selected_next_target"] == SOURCE_NEXT_TARGET
    assert report["surface"] == SURFACE_EVIDENCE
    assert report["source_surface"] == SOURCE_SURFACE_EVIDENCE
    assert report["result_token"] == RESULT_TOKEN
    assert report["fresh_delta_id"] == FRESH_DELTA_ID
    assert report["fresh_delta_kind"] == "counterexample"
    assert report["retained_blocker"] == RETAINED_BLOCKER
    assert report["supplied_route"]["supplied_object"] == (
        "QFTGRClassicalSourceAdmissibilitySemanticPackage"
    )
    assert report["refutation"]["status"] == (
        "renormalized_expectation_value_only_derivation_refuted"
    )
    assert not any(report["nonclaim_boundaries"].values())


def test_registry_rotates_to_classical_source_admissibility_result_review() -> None:
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_forbidden_promotions_closed()
    assert_public_surfaces_match_registry()
    payload = _registry()
    skip_if_not_current_target(payload, LIVE_TARGET)
    state = payload["current_target_state"]

    assert state["previous_live_next_target"] == (
        "review_qft_gr_covariant_conservation_obligation_semantics_result"
    )
    assert state["live_next_target"] == LIVE_TARGET
    assert state["live_next_target_evidence"] == CURRENT_EVIDENCE
    assert state["active_lane"] == (
        "qft_gr_bianchi_compatibility_obligation_semantics_preparation"
    )
    assert "qft_gr_classical_source_admissibility_semantics_preparation" in (
        state["paused_lanes"]
    )

    prep = workstream(
        "qft_gr_classical_source_admissibility_semantics_preparation", payload
    )
    assert prep["status"] == "paused"
    assert prep["authorized_next_strict_target"] == SOURCE_NEXT_TARGET
    assert prep["consumed_target"] == PREVIOUS_TARGET
    assert prep["latest_surface"] == SURFACE_ID
    assert prep["classical_source_admissibility_semantics_surface"] == SURFACE_EVIDENCE
    assert prep["classical_source_admissibility_semantics_report"] == REPORT_EVIDENCE
    assert prep["classical_source_admissibility_semantics_result_token"] == RESULT_TOKEN
    assert prep["supplied_route_available"] == "yes"
    assert prep["renormalized_expectation_value_only_derivation_refuted"] == "yes"
    assert prep["classical_source_admissibility_derived_from_renormalized_expectation_alone"] == "no"
    assert prep["result_review_status"] == "prepared_for_live_result_review"
    assert prep["full_source_map_closure_authorized"] == "no"

    active = workstream(
        "qft_gr_bianchi_compatibility_obligation_semantics_preparation", payload
    )
    assert active["status"] in {"active", "paused"}
    assert active["authorized_next_strict_target"] == LIVE_TARGET
    assert active["consumed_target"] == (
        "review_qft_gr_covariant_conservation_obligation_semantics_result"
    )
    assert active["latest_surface"] == (
        "qft_gr_covariant_conservation_obligation_semantics_result_review_v0"
    )
    assert active["covariant_conservation_obligation_semantics_result_review_token"] == (
        CURRENT_RESULT_TOKEN
    )
    assert active["covariant_conservation_obligation_semantics_authorized"] == (
        "supplied_only_retained"
    )
    assert active["conservation_witness_authorized"] == "no"
    assert active["actual_covariant_conservation_authorized"] == "no"
    assert active["full_source_map_closure_authorized"] == "no"
    assert active["qft_gr_seam_closed"] == "no"
    assert active["phase2_authorized"] == "no"
    assert active["master_action_promotion_authorized"] == "no"

    qft_gr = workstream("qft_gr_source_map", payload)
    assert qft_gr["authorized_next_strict_target"] == LIVE_TARGET
    assert qft_gr["classical_source_admissibility_semantics_surface"] == SURFACE_EVIDENCE
    assert qft_gr["classical_source_admissibility_semantics_result_token"] == RESULT_TOKEN
    assert qft_gr["classical_source_admissibility_renormalized_expectation_only_refuted"] == "yes"
    assert qft_gr["classical_source_admissibility_derived_from_renormalized_expectation_alone"] == "no"
    assert qft_gr["bianchi_compatible_source_proof_authorized"] == "no"
    assert qft_gr["einstein_equation_coupling_authorized"] == "no"
    assert qft_gr["poisson_limit_recovery_authorized"] == "no"

    assert LIVE_TARGET in payload["next_strict_target_coverage"]
    assert PREVIOUS_TARGET in payload["next_strict_target_coverage"]
    edges = {(edge["from"], edge["to"]) for edge in payload["dependency_edges"]}
    assert (
        "qft_gr_classical_source_admissibility_semantics_preparation",
        "qft_gr_classical_source_admissibility_semantics_result_review",
    ) in edges


def test_public_surfaces_track_classical_source_admissibility_slice() -> None:
    for path in [README_PATH, STATE_PATH, ROADMAP_PATH, STRICT_MAP_PATH]:
        text = _read(path)
        assert LIVE_TARGET in text
        assert PREVIOUS_TARGET in text
        assert "QFT_GR_ClassicalSourceAdmissibilitySemantics.lean" in text
        assert RESULT_TOKEN in text

    for path in [SEAM_REGISTRY_PATH, SEAM_INVENTORY_PATH]:
        text = _read(path)
        assert LIVE_TARGET in text
        assert SURFACE_ID in text
        assert REPORT_EVIDENCE in text

    inventory_text = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-QFTGR-CLASSICAL-SOURCE-ADMISSIBILITY-SEMANTICS-v0" in (
        inventory_text
    )
    assert SURFACE_EVIDENCE in inventory_text
    assert REPORT_EVIDENCE in inventory_text
    assert LIVE_TARGET in inventory_text

    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_classical_source_admissibility_semantics_gate.py"
    )
