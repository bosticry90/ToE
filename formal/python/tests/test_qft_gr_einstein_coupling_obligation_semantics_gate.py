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
    / "QFT_GR_EinsteinCouplingObligationSemantics.lean"
)
SOURCE_SURFACE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_BianchiCompatibilityObligationSemanticsResultReview.lean"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_EINSTEIN_COUPLING_OBLIGATION_SEMANTICS_BOUNDED_ATTACK_20260503_v0.json"
)
SOURCE_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_BIANCHI_COMPATIBILITY_OBLIGATION_SEMANTICS_RESULT_REVIEW_20260503_v0.json"
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

SURFACE_ID = "QFT_GR_EINSTEIN_COUPLING_OBLIGATION_SEMANTICS_v0"
PREVIOUS_TARGET = "prepare_qft_gr_einstein_coupling_obligation_semantics_bounded_attack"
SOURCE_REVIEW_TARGET = "review_qft_gr_bianchi_compatibility_obligation_semantics_result"
RESULT_REVIEW_TARGET = "review_qft_gr_einstein_coupling_obligation_semantics_result"
RESULT_TOKEN = "QFT_GR_EINSTEIN_COUPLING_OBLIGATION_SEMANTICS_SUPPLIED_ONLY"
REPORT_ID = "QFT_GR_EINSTEIN_COUPLING_OBLIGATION_SEMANTICS_BOUNDED_ATTACK_20260503_v0"
RETAINED_BLOCKER = "PHASE1-BLOCKER-QFTGR-EINSTEIN-COUPLING-WITNESS-RETAINED"
SOURCE_RETAINED_BLOCKER = (
    "PHASE1-BLOCKER-QFTGR-EINSTEIN-COUPLING-OBLIGATION-SEMANTICS-RETAINED"
)
FRESH_DELTA_ID = (
    "QFT_GR_EINSTEIN_COUPLING_OBLIGATION_SEMANTICS_COUNTEREXAMPLE_FRESH_DELTA_v0"
)
SOURCE_RESULT_TOKEN = (
    "QFT_GR_BIANCHI_COMPATIBILITY_OBLIGATION_SEMANTICS_RESULT_REVIEW_CONSUMED_SUPPLIED_ONLY"
)
ACTIVE_LANE = "qft_gr_einstein_coupling_obligation_semantics_result_review"
PREPARATION_LANE = "qft_gr_einstein_coupling_obligation_semantics_preparation"
SURFACE_EVIDENCE = str(SURFACE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
SOURCE_SURFACE_EVIDENCE = str(SOURCE_SURFACE_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
SOURCE_REPORT_EVIDENCE = str(SOURCE_REPORT_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _registry() -> dict[str, Any]:
    return _json(REGISTRY_PATH)


def test_einstein_coupling_obligation_surface_records_supplied_obligation() -> None:
    text = _read(SURFACE_PATH)

    for token in {
        SURFACE_ID,
        PREVIOUS_TARGET,
        RESULT_REVIEW_TARGET,
        RESULT_TOKEN,
        "QFTGREinsteinCouplingObligationSemanticPackage",
        "QFTGREinsteinCouplingObligationSemanticData",
        "hasEinsteinCouplingObligation",
        "einsteinCouplingSatisfied",
        "supplied_einstein_coupling_obligation_semantics_constructs_package_v0",
        "qft_gr_bianchi_compatibility_obligation_semantics_does_not_force_einstein_coupling_witness_v0",
        "qft_gr_einstein_coupling_obligation_semantics_consumes_live_target_v0",
        "qft_gr_einstein_coupling_obligation_semantics_supplied_route_available_v0",
        "qft_gr_einstein_coupling_obligation_semantics_bianchi_obligation_only_refuted_v0",
        "qft_gr_einstein_coupling_obligation_semantics_retained_as_supplied_v0",
        "qft_gr_einstein_coupling_obligation_semantics_result_token_v0",
        "qft_gr_einstein_coupling_obligation_semantics_selected_next_target_v0",
    }:
        assert token in text


def test_einstein_coupling_obligation_surface_preserves_boundaries() -> None:
    text = _read(SURFACE_PATH)

    for theorem in {
        "qft_gr_einstein_coupling_obligation_semantics_scheme_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_finite_tensor_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_hadamard_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_self_adjoint_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_domain_density_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_conservation_witness_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_actual_conservation_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_bianchi_witness_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_actual_bianchi_compatibility_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_einstein_witness_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_actual_coupling_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_weak_source_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_poisson_limit_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_semiclassical_eq_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_source_map_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_no_seam_closure_v0",
        "qft_gr_einstein_coupling_obligation_semantics_no_semiclassical_gravity_claim_v0",
        "qft_gr_einstein_coupling_obligation_semantics_no_einstein_claim_v0",
        "qft_gr_einstein_coupling_obligation_semantics_phase2_not_authorized_v0",
        "qft_gr_einstein_coupling_obligation_semantics_master_action_not_promoted_v0",
        "qft_gr_einstein_coupling_obligation_semantics_no_empirical_claim_v0",
        "qft_gr_einstein_coupling_obligation_semantics_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_einstein_coupling_obligation_report_records_nonclaim_result() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["current_target"] == PREVIOUS_TARGET
    assert report["consumed_result_review_target"] == SOURCE_REVIEW_TARGET
    assert report["consumed_result_review_token"] == SOURCE_RESULT_TOKEN
    assert report["selected_next_target"] == RESULT_REVIEW_TARGET
    assert report["surface"] == SURFACE_EVIDENCE
    assert report["source_surface"] == SOURCE_SURFACE_EVIDENCE
    assert report["source_report"] == SOURCE_REPORT_EVIDENCE
    assert report["result_token"] == RESULT_TOKEN
    assert report["fresh_delta_id"] == FRESH_DELTA_ID
    assert report["fresh_delta_kind"] == "counterexample"
    assert report["retained_blocker"] == RETAINED_BLOCKER
    assert report["supplied_route"]["supplied_object"] == (
        "QFTGREinsteinCouplingObligationSemanticPackage"
    )
    assert report["supplied_route"]["distinction"] == (
        "has_einstein_coupling_obligation_does_not_imply_has_coupling_witness_or_satisfaction"
    )
    assert report["refutation"]["status"] == (
        "bianchi_compatibility_obligation_only_einstein_coupling_witness_derivation_refuted"
    )
    assert not any(report["nonclaim_boundaries"].values())


def test_registry_rotates_to_einstein_coupling_obligation_result_review() -> None:
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_forbidden_promotions_closed()
    assert_public_surfaces_match_registry()
    payload = _registry()
    skip_if_not_current_target(payload, RESULT_REVIEW_TARGET)
    state = payload["current_target_state"]

    assert state["previous_live_next_target"] == PREVIOUS_TARGET
    assert state["live_next_target"] == RESULT_REVIEW_TARGET
    assert state["live_next_target_evidence"] == SURFACE_EVIDENCE
    assert state["active_lane"] == ACTIVE_LANE
    assert PREPARATION_LANE in state["paused_lanes"]

    prep = workstream(PREPARATION_LANE, payload)
    assert prep["status"] == "paused"
    assert prep["authorized_next_strict_target"] == RESULT_REVIEW_TARGET
    assert prep["consumed_target"] == PREVIOUS_TARGET
    assert prep["latest_surface"] == SURFACE_ID
    assert prep["einstein_coupling_obligation_semantics_surface"] == SURFACE_EVIDENCE
    assert prep["einstein_coupling_obligation_semantics_report"] == REPORT_EVIDENCE
    assert prep["einstein_coupling_obligation_semantics_result_token"] == RESULT_TOKEN
    assert prep["supplied_route_available"] == "yes"
    assert prep["bianchi_obligation_only_einstein_coupling_witness_refuted"] == "yes"
    assert prep["einstein_coupling_witness_derived_from_bianchi_obligation_alone"] == (
        "no"
    )
    assert prep["result_review_status"] == "prepared_for_live_result_review"
    assert prep["einstein_coupling_witness_authorized"] == "no"
    assert prep["actual_einstein_equation_coupling_authorized"] == "no"
    assert prep["weak_curvature_source_identification_authorized"] == "no"
    assert prep["poisson_limit_recovery_authorized"] == "no"
    assert prep["full_source_map_closure_authorized"] == "no"

    active = workstream(ACTIVE_LANE, payload)
    assert active["status"] in {"active", "paused"}
    assert active["authorized_next_strict_target"] == RESULT_REVIEW_TARGET
    assert active["consumed_target"] == PREVIOUS_TARGET
    assert active["latest_surface"] == SURFACE_ID
    assert active["einstein_coupling_obligation_semantics_surface"] == SURFACE_EVIDENCE
    assert active["einstein_coupling_obligation_semantics_result_token"] == RESULT_TOKEN
    assert active["einstein_coupling_witness_authorized"] == "no"
    assert active["actual_einstein_equation_coupling_authorized"] == "no"
    assert active["weak_curvature_source_identification_authorized"] == "no"
    assert active["poisson_limit_recovery_authorized"] == "no"
    assert active["full_source_map_closure_authorized"] == "no"
    assert active["qft_gr_seam_closed"] == "no"
    assert active["phase2_authorized"] == "no"
    assert active["master_action_promotion_authorized"] == "no"

    qft_gr = workstream("qft_gr_source_map", payload)
    assert qft_gr["retained_blocker"] == RETAINED_BLOCKER
    assert qft_gr["authorized_next_strict_target"] == RESULT_REVIEW_TARGET
    assert qft_gr["einstein_coupling_obligation_semantics_surface"] == SURFACE_EVIDENCE
    assert qft_gr["einstein_coupling_obligation_semantics_result_token"] == RESULT_TOKEN
    assert qft_gr["einstein_coupling_obligation_bianchi_only_refuted"] == "yes"
    assert qft_gr["einstein_coupling_witness_derived_from_bianchi_obligation_alone"] == (
        "no"
    )
    assert qft_gr["actual_einstein_equation_coupling_authorized"] == "no"
    assert qft_gr["weak_curvature_source_identification_authorized"] == "no"
    assert qft_gr["poisson_limit_recovery_authorized"] == "no"

    assert RESULT_REVIEW_TARGET in payload["next_strict_target_coverage"]
    assert PREVIOUS_TARGET in payload["next_strict_target_coverage"]
    assert RETAINED_BLOCKER in payload["retained_blocker_coverage"]
    assert SOURCE_RETAINED_BLOCKER in payload["retained_blocker_coverage"]
    edges = {(edge["from"], edge["to"]) for edge in payload["dependency_edges"]}
    assert (PREPARATION_LANE, ACTIVE_LANE) in edges


def test_public_surfaces_track_einstein_coupling_obligation() -> None:
    for path in [README_PATH, STATE_PATH, ROADMAP_PATH, STRICT_MAP_PATH]:
        text = _read(path)
        assert PREVIOUS_TARGET in text
        assert RESULT_REVIEW_TARGET in text
        assert "QFT_GR_EinsteinCouplingObligationSemantics.lean" in text
        assert RESULT_TOKEN in text

    for path in [SEAM_REGISTRY_PATH, SEAM_INVENTORY_PATH]:
        text = _read(path)
        assert RESULT_REVIEW_TARGET in text
        assert SURFACE_ID in text
        assert REPORT_EVIDENCE in text

    inventory_text = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-QFTGR-EINSTEIN-COUPLING-OBLIGATION-v0" in inventory_text
    assert SURFACE_EVIDENCE in inventory_text
    assert REPORT_EVIDENCE in inventory_text
    assert RESULT_REVIEW_TARGET in inventory_text

    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_einstein_coupling_obligation_semantics_gate.py"
    )
