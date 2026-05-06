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
    / "QFT_GR_ClassicalSourceAdmissibilitySemanticsResultReview.lean"
)
SOURCE_SURFACE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_ClassicalSourceAdmissibilitySemantics.lean"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_CLASSICAL_SOURCE_ADMISSIBILITY_SEMANTICS_RESULT_REVIEW_20260503_v0.json"
)
SOURCE_REPORT_PATH = (
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

SURFACE_ID = "qft_gr_classical_source_admissibility_semantics_result_review_v0"
PREVIOUS_TARGET = "review_qft_gr_classical_source_admissibility_semantics_result"
SELECTED_NEXT_TARGET = (
    "prepare_qft_gr_covariant_conservation_obligation_semantics_bounded_attack"
)
CURRENT_PREVIOUS_TARGET = "review_qft_gr_covariant_conservation_obligation_semantics_result"
LIVE_TARGET = "prepare_qft_gr_bianchi_compatibility_obligation_semantics_bounded_attack"
CURRENT_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_CovariantConservationObligationSemanticsResultReview.lean"
)
CURRENT_SURFACE_ID = "qft_gr_covariant_conservation_obligation_semantics_result_review_v0"
CURRENT_RESULT_TOKEN = (
    "QFT_GR_COVARIANT_CONSERVATION_OBLIGATION_SEMANTICS_RESULT_REVIEW_CONSUMED_SUPPLIED_ONLY"
)
SOURCE_RESULT_TOKEN = "QFT_GR_CLASSICAL_SOURCE_ADMISSIBILITY_SEMANTICS_SUPPLIED_ONLY"
REVIEW_RESULT_TOKEN = (
    "QFT_GR_CLASSICAL_SOURCE_ADMISSIBILITY_SEMANTICS_RESULT_REVIEW_CONSUMED_SUPPLIED_ONLY"
)
REPORT_ID = "QFT_GR_CLASSICAL_SOURCE_ADMISSIBILITY_SEMANTICS_RESULT_REVIEW_20260503_v0"
RETAINED_BLOCKER = (
    "PHASE1-BLOCKER-QFTGR-COVARIANT-CONSERVATION-OBLIGATION-SEMANTICS-RETAINED"
)
CURRENT_RETAINED_BLOCKER = (
    "PHASE1-BLOCKER-QFTGR-BIANCHI-COMPATIBILITY-OBLIGATION-SEMANTICS-RETAINED"
)
SOURCE_RETAINED_BLOCKER = (
    "PHASE1-BLOCKER-QFTGR-CLASSICAL-SOURCE-ADMISSIBILITY-SEMANTICS-RETAINED"
)
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


def test_classical_source_admissibility_result_review_surface_consumes_result() -> None:
    text = _read(SURFACE_PATH)

    for token in {
        SURFACE_ID,
        PREVIOUS_TARGET,
        SELECTED_NEXT_TARGET,
        SOURCE_RESULT_TOKEN,
        REVIEW_RESULT_TOKEN,
        "QFTGRClassicalSourceAdmissibilityResultReviewStatus",
        "QFTGRClassicalSourceAdmissibilityResultReviewDecision",
        "acceptSuppliedOnlyAndPrepareCovariantConservationObligationSemantics",
        "qft_gr_classical_source_admissibility_result_review_consumes_live_target_v0",
        "qft_gr_classical_source_admissibility_result_review_completed_v0",
        "qft_gr_classical_source_admissibility_result_review_accepts_supplied_only_v0",
        "qft_gr_classical_source_admissibility_result_review_renormalized_only_refuted_v0",
        "qft_gr_classical_source_admissibility_result_review_retained_as_supplied_v0",
        "qft_gr_classical_source_admissibility_result_review_token_v0",
        "qft_gr_classical_source_admissibility_result_review_selected_decision_v0",
        "qft_gr_classical_source_admissibility_result_review_selected_next_target_v0",
    }:
        assert token in text


def test_classical_source_admissibility_result_review_preserves_boundaries() -> None:
    text = _read(SURFACE_PATH)

    for theorem in {
        "qft_gr_classical_source_admissibility_result_review_same_lane_not_authorized_v0",
        "qft_gr_classical_source_admissibility_result_review_scheme_not_authorized_v0",
        "qft_gr_classical_source_admissibility_result_review_finiteness_not_authorized_v0",
        "qft_gr_classical_source_admissibility_result_review_hadamard_not_authorized_v0",
        "qft_gr_classical_source_admissibility_result_review_self_adjoint_not_authorized_v0",
        "qft_gr_classical_source_admissibility_result_review_domain_density_not_authorized_v0",
        "qft_gr_classical_source_admissibility_result_review_conservation_obligation_not_authorized_v0",
        "qft_gr_classical_source_admissibility_result_review_conservation_not_authorized_v0",
        "qft_gr_classical_source_admissibility_result_review_bianchi_not_authorized_v0",
        "qft_gr_classical_source_admissibility_result_review_einstein_coupling_not_authorized_v0",
        "qft_gr_classical_source_admissibility_result_review_weak_source_not_authorized_v0",
        "qft_gr_classical_source_admissibility_result_review_poisson_not_authorized_v0",
        "qft_gr_classical_source_admissibility_result_review_semiclassical_eq_not_authorized_v0",
        "qft_gr_classical_source_admissibility_result_review_source_map_not_authorized_v0",
        "qft_gr_classical_source_admissibility_result_review_no_seam_closure_v0",
        "qft_gr_classical_source_admissibility_result_review_no_semiclassical_claim_v0",
        "qft_gr_classical_source_admissibility_result_review_no_einstein_claim_v0",
        "qft_gr_classical_source_admissibility_result_review_phase2_not_authorized_v0",
        "qft_gr_classical_source_admissibility_result_review_master_action_not_promoted_v0",
        "qft_gr_classical_source_admissibility_result_review_no_empirical_claim_v0",
        "qft_gr_classical_source_admissibility_result_review_manifest_not_enrolled_v0",
    }:
        assert theorem in text


def test_classical_source_admissibility_result_review_report_records_selection() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["current_target"] == PREVIOUS_TARGET
    assert report["consumed_result_token"] == SOURCE_RESULT_TOKEN
    assert report["review_result_token"] == REVIEW_RESULT_TOKEN
    assert report["review_surface"] == SURFACE_EVIDENCE
    assert report["source_surface"] == SOURCE_SURFACE_EVIDENCE
    assert report["source_report"] == SOURCE_REPORT_EVIDENCE
    assert report["selected_next_target"] == SELECTED_NEXT_TARGET
    assert report["selected_decision"] == (
        "accept_supplied_only_and_prepare_covariant_conservation_obligation_semantics"
    )
    assert report["review_result"] == (
        "supplied_only_classical_source_admissibility_result_consumed"
    )
    assert report["accepted_result"]["supplied_object"] == (
        "QFTGRClassicalSourceAdmissibilitySemanticPackage"
    )
    assert report["retained_blocker"] == RETAINED_BLOCKER
    assert report["refutation_confirmed"]["status"] == (
        "renormalized_expectation_value_only_derivation_refuted"
    )
    assert not any(report["nonclaim_boundaries"].values())


def test_registry_rotates_to_covariant_conservation_obligation_preparation() -> None:
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
    assert "qft_gr_classical_source_admissibility_semantics_result_review" in (
        state["paused_lanes"]
    )

    review = workstream(
        "qft_gr_classical_source_admissibility_semantics_result_review", payload
    )
    assert review["status"] == "paused"
    assert review["authorized_next_strict_target"] == SELECTED_NEXT_TARGET
    assert review["consumed_target"] == PREVIOUS_TARGET
    assert review["latest_surface"] == SURFACE_ID
    assert review["result_review_surface"] == SURFACE_EVIDENCE
    assert review["result_review_report"] == REPORT_EVIDENCE
    assert review["review_result_token"] == REVIEW_RESULT_TOKEN
    assert review["review_result"] == (
        "supplied_only_classical_source_admissibility_result_consumed"
    )
    assert review["review_decision"] == (
        "accept_supplied_only_and_prepare_covariant_conservation_obligation_semantics"
    )
    assert review["covariant_conservation_obligation_semantics_authorized"] == "no"
    assert review["covariant_conservation_authorized"] == "no"
    assert review["full_source_map_closure_authorized"] == "no"

    active = workstream(
        "qft_gr_bianchi_compatibility_obligation_semantics_preparation", payload
    )
    assert active["status"] in {"active", "paused"}
    assert active["authorized_next_strict_target"] == LIVE_TARGET
    assert active["consumed_target"] == CURRENT_PREVIOUS_TARGET
    assert active["latest_surface"] == CURRENT_SURFACE_ID
    assert active["covariant_conservation_obligation_semantics_result_review_token"] == (
        CURRENT_RESULT_TOKEN
    )
    assert active["preparation_scope"] == (
        "bianchi_compatibility_obligation_semantics_surface_only"
    )
    assert active["covariant_conservation_obligation_semantics_authorized"] == (
        "supplied_only_retained"
    )
    assert active["actual_covariant_conservation_authorized"] == "no"
    assert active["bianchi_compatible_source_proof_authorized"] == "no"
    assert active["einstein_equation_coupling_authorized"] == "no"
    assert active["full_source_map_closure_authorized"] == "no"
    assert active["qft_gr_seam_closed"] == "no"
    assert active["phase2_authorized"] == "no"
    assert active["master_action_promotion_authorized"] == "no"

    qft_gr = workstream("qft_gr_source_map", payload)
    assert qft_gr["retained_blocker"] == CURRENT_RETAINED_BLOCKER
    assert qft_gr["classical_source_admissibility_semantics_result_review_status"] == (
        "completed"
    )
    assert qft_gr["classical_source_admissibility_semantics_result_review_evidence"] == (
        SURFACE_EVIDENCE
    )
    assert qft_gr["classical_source_admissibility_semantics_result_review_report"] == (
        REPORT_EVIDENCE
    )
    assert qft_gr["covariant_conservation_obligation_semantics_preparation_target"] == (
        SELECTED_NEXT_TARGET
    )
    assert qft_gr["covariant_conservation_authorized"] == "no"
    assert qft_gr["full_source_map_semantic_closure_authorized"] == "no"

    assert SELECTED_NEXT_TARGET in payload["next_strict_target_coverage"]
    assert LIVE_TARGET in payload["next_strict_target_coverage"]
    assert PREVIOUS_TARGET in payload["next_strict_target_coverage"]
    assert RETAINED_BLOCKER in payload["retained_blocker_coverage"]
    assert SOURCE_RETAINED_BLOCKER in payload["retained_blocker_coverage"]
    edges = {(edge["from"], edge["to"]) for edge in payload["dependency_edges"]}
    assert (
        "qft_gr_covariant_conservation_obligation_semantics_result_review",
        "qft_gr_bianchi_compatibility_obligation_semantics_preparation",
    ) in edges


def test_public_surfaces_track_result_review_and_next_preparation() -> None:
    for path in [README_PATH, STATE_PATH, ROADMAP_PATH, STRICT_MAP_PATH]:
        text = _read(path)
        assert SELECTED_NEXT_TARGET in text
        assert PREVIOUS_TARGET in text
        assert "QFT_GR_ClassicalSourceAdmissibilitySemanticsResultReview.lean" in text
        assert REVIEW_RESULT_TOKEN in text

    for path in [SEAM_REGISTRY_PATH, SEAM_INVENTORY_PATH]:
        text = _read(path)
        assert SELECTED_NEXT_TARGET in text
        assert PREVIOUS_TARGET in text
        assert SURFACE_ID in text
        assert REPORT_EVIDENCE in text

    inventory_text = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-QFTGR-CLASSICAL-SOURCE-ADMISSIBILITY-RESULT-REVIEW-v0" in (
        inventory_text
    )
    assert SURFACE_EVIDENCE in inventory_text
    assert REPORT_EVIDENCE in inventory_text
    assert SELECTED_NEXT_TARGET in inventory_text

    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_classical_source_admissibility_semantics_result_review_gate.py"
    )
