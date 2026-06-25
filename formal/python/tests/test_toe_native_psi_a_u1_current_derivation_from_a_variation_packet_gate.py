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
from formal.python.tools.toe_native_psi_a_u1_current_derivation_from_A_variation_packet_report import (
    A_VARIATION_RESIDUAL,
    ACTION_BLOCK_RESULT_REVIEW_OUTCOME,
    ACTION_BLOCK_RESULT_REVIEW_PATH,
    ACTION_BLOCK_STATEMENT,
    BLOCKED_CLAIMS,
    BOUNDED_ROUTE_SHAPE,
    CONSUMED_TARGET,
    COVARIANT_DERIVATIVE_POLICY,
    CURRENT_CANDIDATE_FROM_A_VARIATION,
    CURRENT_DERIVATION_PACKET_RESULT,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    EULER_RESIDUAL_SHAPE,
    FIELD_STRENGTH_POLICY,
    GAUGE_A_VARIATION_TERM,
    GAUGE_COVARIANT_DERIVATIVE_TRANSFORM,
    GAUGE_TRANSFORMATION_POLICY,
    INTERACTION_TERM_SHAPE,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_A_DEPENDENT_TERM,
    MATTER_A_VARIATION_TERM,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    SELECTED_INTERACTION_ROUTE,
    VARIATION_VARIABLE,
    build_toe_native_psi_a_u1_current_derivation_from_A_variation_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_psi_a_u1_current_derivation_from_A_variation_packet_report.py"
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


def test_psi_a_u1_current_derivation_from_A_variation_files_exist() -> None:
    for path in [
        ACTION_BLOCK_RESULT_REVIEW_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_psi_a_u1_current_derivation_from_A_variation_packet_builds() -> None:
    review = _json(ACTION_BLOCK_RESULT_REVIEW_PATH)
    packet = _json(DEFAULT_OUT)
    assert review["outcome_id"] == ACTION_BLOCK_RESULT_REVIEW_OUTCOME
    assert review["selected_next_target"] == CONSUMED_TARGET

    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["current_derivation_packet_result"] == CURRENT_DERIVATION_PACKET_RESULT
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert build_toe_native_psi_a_u1_current_derivation_from_A_variation_packet() == packet


def test_psi_a_u1_current_derivation_from_A_variation_records_route_shape() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_interaction_route"] == SELECTED_INTERACTION_ROUTE
    assert packet["action_block_statement"] == ACTION_BLOCK_STATEMENT
    assert packet["covariant_derivative_policy"] == COVARIANT_DERIVATIVE_POLICY
    assert packet["field_strength_policy"] == FIELD_STRENGTH_POLICY
    assert packet["gauge_transformation_policy"] == GAUGE_TRANSFORMATION_POLICY
    assert packet["gauge_covariant_derivative_transform"] == (
        GAUGE_COVARIANT_DERIVATIVE_TRANSFORM
    )
    assert packet["interaction_term_shape"] == INTERACTION_TERM_SHAPE
    assert packet["variation_variable"] == VARIATION_VARIABLE
    assert packet["matter_A_dependent_term"] == MATTER_A_DEPENDENT_TERM
    assert packet["matter_A_variation_term"] == MATTER_A_VARIATION_TERM
    assert packet["gauge_A_variation_term"] == GAUGE_A_VARIATION_TERM
    assert packet["Euler_residual_shape"] == EULER_RESIDUAL_SHAPE
    assert packet["A_variation_residual"] == A_VARIATION_RESIDUAL
    assert packet["current_candidate_from_A_variation"] == (
        CURRENT_CANDIDATE_FROM_A_VARIATION
    )
    assert packet["bounded_route_shape"] == BOUNDED_ROUTE_SHAPE
    for key in [
        "current_derivation_packet_prepared",
        "A_variation_current_derivation_packet_prepared",
        "A_variation_route_recorded",
        "A_variation_result_recorded",
        "A_variation_current_candidate_recorded",
        "bounded_A_variation_residual_recorded",
        "matter_A_dependent_term_identified",
        "matter_A_variation_term_recorded",
        "gauge_A_variation_term_recorded",
        "candidate_current_identified",
        "bounded_sourced_gauge_route_shape_recorded",
        "sourced_gauge_equation_route_shape_recorded",
        "psi_supplies_candidate_source_current",
        "selected_conventions_preserved",
        "result_review_preparation_authorized",
    ]:
        assert packet[key] is True, key


def test_psi_a_u1_current_derivation_from_A_variation_preserves_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["blocked_claims"] == BLOCKED_CLAIMS
    assert packet["blocked_claim_count"] == 13
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
        "full_sourced_maxwell_derivation_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "quantized_electromagnetism_claimed",
        "standard_model_derivation_claimed",
        "phase2_authorized",
        "empirical_validation_claimed",
        "master_action_promoted",
    ]:
        assert packet[key] is False, key
    for phrase in [
        "bounded A-variation current packet only",
        "records a candidate current and route shape",
        "no current conservation proof",
        "no psi variation or Dirac derivation",
        "no stress-energy derivation",
        "no exchange identity",
        "no total conservation proof",
        "no C_exchange closeout",
        "no sourced Maxwell closure",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no quantized electromagnetism",
        "no Standard Model derivation",
        "no Phase 2 authorization",
        "no empirical validation",
        "no master-action promotion",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert phrase in packet["non_claim_boundary"], phrase


def test_psi_a_u1_current_derivation_from_A_variation_rotates_to_result_review() -> None:
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
    assert consumed["current_derivation_packet_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["A_variation_current_candidate_recorded"] == "yes"
    assert consumed["bounded_A_variation_residual_recorded"] == "yes"
    assert consumed["J_nu_derived"] == "no"
    assert consumed["current_conservation_proved"] == "no"
    assert consumed["sourced_maxwell_closure_claimed"] == "no"
    assert consumed["matter_gauge_exchange_proved"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["consumed_current_derivation_packet_result"] == OUTCOME_ID
    assert active_row["packet_result"] == "PENDING"
    assert active_row["result_review_pending"] == "yes"
    assert active_row["result_review_completed"] == "no"
    assert active_row["current_derivation_packet_prepared"] == "yes"
    assert active_row["A_variation_current_candidate_recorded"] == "yes"
    assert active_row["bounded_sourced_gauge_route_shape_recorded"] == "yes"
    assert active_row["current_candidate_from_A_variation"] == (
        CURRENT_CANDIDATE_FROM_A_VARIATION
    )
    assert active_row["bounded_route_shape"] == BOUNDED_ROUTE_SHAPE
    assert active_row["J_nu_derived"] == "no"
    assert active_row["current_conservation_proved"] == "no"
    assert active_row["sourced_maxwell_closure_claimed"] == "no"
    assert active_row["matter_gauge_exchange_proved"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_psi_a_u1_current_derivation_from_A_variation_lean_and_surface_mirrors() -> None:
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
        CURRENT_DERIVATION_PACKET_RESULT,
        PACKET_CLASSIFICATION,
        "ToeNativePsiAU1CurrentDerivationFromAVariationPacket",
        NEXT_TARGET,
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "review_toe_native_psi_A_u1_current_derivation_from_A_variation_packet_result",
        "PREVIOUS_LIVE_NEXT_TARGET_v0: "
        "prepare_toe_native_psi_A_u1_current_derivation_from_A_variation_packet",
        ACTION_BLOCK_STATEMENT,
        COVARIANT_DERIVATIVE_POLICY,
        MATTER_A_DEPENDENT_TERM,
        MATTER_A_VARIATION_TERM,
        GAUGE_A_VARIATION_TERM,
        EULER_RESIDUAL_SHAPE,
        CURRENT_CANDIDATE_FROM_A_VARIATION,
        BOUNDED_ROUTE_SHAPE,
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


def test_psi_a_u1_current_derivation_from_A_variation_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_psi_a_u1_current_derivation_from_a_variation_packet_gate.py"
    )
