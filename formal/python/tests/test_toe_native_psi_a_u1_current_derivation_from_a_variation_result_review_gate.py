from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_current_target_consistent,
    assert_focused_gate_not_manifest_enrolled,
    assert_frontier_matches_registry,
    assert_public_surfaces_match_registry,
)
from formal.python.tools.toe_native_psi_a_u1_current_derivation_from_A_variation_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    A_VARIATION_RESIDUAL,
    BLOCKED_CLAIMS,
    BOUNDED_ROUTE_SHAPE,
    CONSUMED_TARGET,
    COVARIANT_DERIVATIVE_POLICY,
    CURRENT_CANDIDATE_FROM_A_VARIATION,
    CURRENT_CONSERVATION_QUESTION,
    CURRENT_DERIVATION_PACKET_RESULT,
    CURRENT_PACKET_OUTCOME,
    CURRENT_PACKET_PATH,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    EULER_RESIDUAL_SHAPE,
    FIELD_EQUATION_ROUTE_PREVIEW,
    GAUGE_SYMMETRY_ROUTE_PREVIEW,
    GAUGE_TRANSFORMATION_POLICY,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_OBLIGATION_PACKET_EXPECTED_OUTCOME,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    REVIEW_RESULT,
    SCHEMA_ID,
    build_toe_native_psi_a_u1_current_derivation_from_A_variation_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_psi_a_u1_current_derivation_from_A_variation_result_review_report.py"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
TOE_FORMAL_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
FRONTIER_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CrossPillarClosureFrontier.lean"
)
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STRICT_MAP_PATH = (
    REPO_ROOT / "formal" / "docs" / "lanes" / "STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8-sig")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _workstream(payload: dict, workstream_id: str) -> dict:
    for row in payload["workstreams"]:
        if row["workstream_id"] == workstream_id:
            return row
    raise AssertionError(f"Missing workstream: {workstream_id}")


def test_psi_a_u1_current_derivation_from_A_variation_result_review_files_exist() -> None:
    for path in [
        CURRENT_PACKET_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_psi_a_u1_current_derivation_from_A_variation_result_review_accepts_packet() -> None:
    packet = _json(CURRENT_PACKET_PATH)
    review = _json(DEFAULT_OUT)
    assert packet["outcome_id"] == CURRENT_PACKET_OUTCOME
    assert packet["selected_next_target"] == CONSUMED_TARGET

    assert review["schema_id"] == SCHEMA_ID
    assert review["packet_id"] == PACKET_ID
    assert review["prepared"] is True
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["review_result"] == REVIEW_RESULT
    assert review["packet_classification"] == PACKET_CLASSIFICATION
    assert review["consumed_target"] == CONSUMED_TARGET
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert (
        build_toe_native_psi_a_u1_current_derivation_from_A_variation_result_review()
        == review
    )


def test_psi_a_u1_current_derivation_from_A_variation_result_review_accepts_route_only() -> None:
    review = _json(DEFAULT_OUT)
    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert review["current_derivation_packet_result"] == CURRENT_DERIVATION_PACKET_RESULT
    assert review["A_variation_residual"] == A_VARIATION_RESIDUAL
    assert review["Euler_residual_shape"] == EULER_RESIDUAL_SHAPE
    assert review["current_candidate_from_A_variation"] == (
        CURRENT_CANDIDATE_FROM_A_VARIATION
    )
    assert review["bounded_route_shape"] == BOUNDED_ROUTE_SHAPE
    assert review["covariant_derivative_policy"] == COVARIANT_DERIVATIVE_POLICY
    assert review["gauge_transformation_policy"] == GAUGE_TRANSFORMATION_POLICY
    for key in [
        "A_variation_route_shape_accepted",
        "A_variation_route_shape_recorded",
        "current_candidate_accepted",
        "current_candidate_indexed",
        "candidate_current_from_A_variation_accepted",
        "sourced_gauge_residual_shape_accepted",
        "sourced_gauge_residual_shape_recorded",
        "bounded_current_route_accepted",
        "bounded_sourced_gauge_route_shape_accepted",
        "plus_sign_D_mu_convention_preserved",
        "selected_conventions_preserved",
    ]:
        assert review[key] is True, key


def test_psi_a_u1_current_derivation_from_A_variation_result_review_selects_obligation_packet() -> None:
    review = _json(DEFAULT_OUT)
    assert review["current_conservation_question"] == CURRENT_CONSERVATION_QUESTION
    assert review["gauge_symmetry_route_preview"] == GAUGE_SYMMETRY_ROUTE_PREVIEW
    assert review["field_equation_route_preview"] == FIELD_EQUATION_ROUTE_PREVIEW
    assert (
        review["next_obligation_packet_expected_outcome"]
        == NEXT_OBLIGATION_PACKET_EXPECTED_OUTCOME
    )
    assert review["current_conservation_obligation_packet_selected"] is True
    assert review["current_conservation_obligation_packet_preparation_authorized"] is True
    assert review["current_conservation_route_packet_selected"] is False
    assert review["gauge_symmetry_route_indexed"] is True
    assert review["field_equation_route_indexed"] is True


def test_psi_a_u1_current_derivation_from_A_variation_result_review_preserves_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    assert review["blocked_claims"] == BLOCKED_CLAIMS
    assert review["blocked_claim_count"] == 12
    for key in [
        "current_conservation_proved",
        "psi_variation_result_derived",
        "dirac_equation_derived",
        "stress_energy_derived",
        "psi_stress_energy_derived",
        "exchange_identity_proved",
        "A_psi_exchange_identity_proved",
        "total_conservation_proved",
        "total_stress_energy_conservation_proved",
        "C_exchange_closeout",
        "C_exchange_definition_closeout",
        "sourced_maxwell_closure_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "phase2_authorized",
        "empirical_validation_claimed",
        "master_action_promoted",
    ]:
        assert review[key] is False, key
    for phrase in [
        "A-variation current result review only",
        "accepts the candidate current and bounded route shape",
        "no current conservation proof",
        "no psi variation or Dirac derivation",
        "no stress-energy derivation",
        "no exchange identity",
        "no total conservation proof",
        "no C_exchange closeout",
        "no sourced Maxwell closure",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no Phase 2 authorization",
        "no empirical validation",
        "no master-action promotion",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert phrase in review["non_claim_boundary"], phrase


def test_psi_a_u1_current_derivation_from_A_variation_result_review_rotates_to_conservation_obligation() -> None:
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()

    registry = _json(REGISTRY_PATH)
    state = registry["current_target_state"]
    active = [row for row in registry["workstreams"] if row.get("status") == "active"]
    assert len(active) == 1
    assert state["previous_live_next_target"] == CONSUMED_TARGET
    assert state["live_next_target"] == NEXT_TARGET
    assert state["active_lane"] == NEXT_TARGET
    assert state["live_next_target_evidence"] == str(
        LEAN_PACKET_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert state["live_next_target_report"] == str(
        DEFAULT_OUT.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert state["live_next_target_kind"] == NEXT_TARGET_KIND
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["packet_result"] == OUTCOME_ID
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["A_variation_route_shape_accepted"] == "yes"
    assert consumed["current_candidate_accepted"] == "yes"
    assert consumed["current_conservation_proved"] == "no"
    assert consumed["sourced_maxwell_closure_claimed"] == "no"
    assert consumed["matter_gauge_exchange_proved"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["consumed_current_derivation_result_review"] == OUTCOME_ID
    assert active_row["packet_result"] == "PENDING"
    assert active_row["current_conservation_obligation_packet_result"] == "PENDING"
    assert active_row["current_conservation_obligation_packet_preparation_authorized"] == "yes"
    assert active_row["current_conservation_obligation_packet_prepared"] == "no"
    assert active_row["current_conservation_question"] == CURRENT_CONSERVATION_QUESTION
    assert active_row["gauge_symmetry_route_preview"] == GAUGE_SYMMETRY_ROUTE_PREVIEW
    assert active_row["field_equation_route_preview"] == FIELD_EQUATION_ROUTE_PREVIEW
    assert active_row["current_conservation_proved"] == "no"
    assert active_row["sourced_maxwell_closure_claimed"] == "no"
    assert active_row["matter_gauge_exchange_proved"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_psi_a_u1_current_derivation_from_A_variation_result_review_lean_and_surface_mirrors() -> None:
    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            DEFAULT_OUT,
            LEAN_PACKET_PATH,
            QFTGR_AGGREGATE_PATH,
            CURRENT_TARGET_AGGREGATE_PATH,
            RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
            TOE_FORMAL_PATH,
            REGISTRY_PATH,
            SURFACES_PATH,
            FRONTIER_PATH,
            README_PATH,
            STATE_PATH,
            ROADMAP_PATH,
            STRICT_MAP_PATH,
        ]
    )
    for token in [
        PACKET_ID,
        OUTCOME_ID,
        REVIEW_RESULT,
        PACKET_CLASSIFICATION,
        "ToeNativePsiAU1CurrentDerivationFromAVariationResultReview",
        NEXT_TARGET,
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_toe_native_psi_A_u1_current_conservation_obligation_packet",
        "PREVIOUS_LIVE_NEXT_TARGET_v0: "
        "review_toe_native_psi_A_u1_current_derivation_from_A_variation_packet_result",
        A_VARIATION_RESIDUAL,
        CURRENT_CANDIDATE_FROM_A_VARIATION,
        BOUNDED_ROUTE_SHAPE,
        CURRENT_CONSERVATION_QUESTION,
        GAUGE_SYMMETRY_ROUTE_PREVIEW,
        FIELD_EQUATION_ROUTE_PREVIEW,
        "no current conservation proof",
        "no psi variation or Dirac derivation",
        "no stress-energy derivation",
        "no exchange identity",
        "no total conservation proof",
        "no C_exchange closeout",
        "no sourced Maxwell closure",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no master-action promotion",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert token in joined


def test_psi_a_u1_current_derivation_from_A_variation_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_psi_a_u1_current_derivation_from_a_variation_result_review_gate.py"
    )
