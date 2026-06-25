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
from formal.python.tools.toe_native_psi_a_u1_interaction_action_block_definition_result_review_report import (
    ACTION_BLOCK_PACKET_OUTCOME,
    ACTION_BLOCK_PACKET_PATH,
    ACTION_BLOCK_STATEMENT,
    ADJOINT_POLICY,
    BLOCKED_CLAIMS,
    CONSUMED_TARGET,
    COVARIANT_DERIVATIVE_POLICY,
    CURRENT_CANDIDATE_PREVIEW,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    FIELD_DOMAIN_POLICY,
    FIELD_STRENGTH_POLICY,
    GAMMA_MATRIX_POLICY,
    GAUGE_COVARIANT_DERIVATIVE_TRANSFORM,
    GAUGE_TRANSFORMATION_POLICY,
    INTERACTION_TERM_SHAPE,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    MATTER_BLOCK_EXPANSION,
    MINIMAL_COUPLING_EXPANSION,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    REVIEW_RESULT,
    SCHEMA_ID,
    SELECTED_INTERACTION_ROUTE,
    SPIN_CONNECTION_POLICY,
    TETRAD_POLICY,
    build_toe_native_psi_a_u1_interaction_action_block_definition_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_psi_a_u1_interaction_action_block_definition_result_review_report.py"
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
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _workstream(payload: dict, workstream_id: str) -> dict:
    for row in payload["workstreams"]:
        if row["workstream_id"] == workstream_id:
            return row
    raise AssertionError(f"Missing workstream: {workstream_id}")


def test_psi_a_u1_action_block_definition_result_review_files_exist() -> None:
    for path in [
        ACTION_BLOCK_PACKET_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_psi_a_u1_action_block_definition_result_review_accepts_packet() -> None:
    action_packet = _json(ACTION_BLOCK_PACKET_PATH)
    review = _json(DEFAULT_OUT)
    assert action_packet["outcome_id"] == ACTION_BLOCK_PACKET_OUTCOME
    assert action_packet["selected_next_target"] == CONSUMED_TARGET

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
        build_toe_native_psi_a_u1_interaction_action_block_definition_result_review()
        == review
    )


def test_psi_a_u1_action_block_definition_result_review_preserves_surfaces() -> None:
    review = _json(DEFAULT_OUT)
    assert review["selected_interaction_route"] == SELECTED_INTERACTION_ROUTE
    assert review["action_block_statement"] == ACTION_BLOCK_STATEMENT
    assert review["covariant_derivative_policy"] == COVARIANT_DERIVATIVE_POLICY
    assert review["field_strength_policy"] == FIELD_STRENGTH_POLICY
    assert review["gauge_transformation_policy"] == GAUGE_TRANSFORMATION_POLICY
    assert review["gauge_covariant_derivative_transform"] == (
        GAUGE_COVARIANT_DERIVATIVE_TRANSFORM
    )
    assert review["minimal_coupling_expansion"] == MINIMAL_COUPLING_EXPANSION
    assert review["matter_block_expansion"] == MATTER_BLOCK_EXPANSION
    assert review["interaction_term_shape"] == INTERACTION_TERM_SHAPE
    assert review["current_candidate_preview"] == CURRENT_CANDIDATE_PREVIEW
    assert review["adjoint_policy"] == ADJOINT_POLICY
    assert review["gamma_matrix_policy"] == GAMMA_MATRIX_POLICY
    assert review["tetrad_policy"] == TETRAD_POLICY
    assert review["spin_connection_policy"] == SPIN_CONNECTION_POLICY
    assert review["field_domain_policy"] == FIELD_DOMAIN_POLICY
    for key in [
        "action_block_definition_accepted",
        "action_block_defined_confirmed",
        "plus_sign_D_mu_convention_preserved",
        "matched_gauge_transform_policy_preserved",
        "F_equals_dA_preserved",
        "psibar_convention_indexed",
        "spin_geometry_placeholders_preserved",
        "domain_and_boundary_policy_preserved",
        "current_candidate_indexed_only",
        "stress_energy_names_indexed_only",
        "exchange_policy_indexed_only",
        "interaction_term_recorded_as_future_variation_input",
        "direct_A_variation_current_derivation_packet_selected",
        "current_derivation_packet_preparation_authorized",
    ]:
        assert review[key] is True, key
    assert review["action_variation_policy_packet_selected"] is False


def test_psi_a_u1_action_block_definition_result_review_preserves_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    assert review["blocked_claims"] == BLOCKED_CLAIMS
    assert review["blocked_claim_count"] == 15
    for key in [
        "A_variation_result_derived",
        "A_variation_current_derived",
        "psi_variation_result_derived",
        "psi_field_equation_derived",
        "J_nu_derived",
        "current_derived",
        "current_conservation_proved",
        "sourced_maxwell_equation_derived",
        "dirac_equation_derived",
        "psi_stress_energy_derived",
        "exchange_proof_claimed",
        "total_conservation_proved",
        "total_stress_energy_conservation_proved",
        "C_exchange_closeout",
        "C_exchange_definition_closeout",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "phase2_authorized",
        "empirical_validation_claimed",
        "master_action_promoted",
    ]:
        assert review[key] is False, key
    for phrase in [
        "result review only",
        "no A-variation result",
        "no psi variation result",
        "no J^nu derivation",
        "no current conservation proof",
        "no sourced Maxwell derivation",
        "no Dirac derivation",
        "no psi stress-energy derivation",
        "no exchange proof",
        "no total conservation proof",
        "no C_exchange closeout",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no Phase 2 authorization",
        "no empirical validation",
        "no master-action promotion",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert phrase in review["non_claim_boundary"], phrase


def test_psi_a_u1_action_block_definition_result_review_validation_policy_is_bounded() -> None:
    review = _json(DEFAULT_OUT)
    policy = review["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert policy["full_toeformal_aggregate_passed"] is False
    assert policy["full_toeformal_aggregate_failed"] is False
    assert policy["full_toeformal_aggregate_timed_out"] is False


def test_psi_a_u1_action_block_definition_result_review_rotates_to_current_derivation_packet() -> None:
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
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["action_block_definition_accepted"] == "yes"
    assert consumed["J_nu_derived"] == "no"
    assert consumed["sourced_maxwell_equation_derived"] == "no"
    assert consumed["matter_gauge_exchange_proved"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["consumed_action_block_definition_result_review"] == OUTCOME_ID
    assert active_row["packet_result"] == "PENDING"
    assert active_row["current_derivation_packet_preparation_authorized"] == "yes"
    assert active_row["current_derivation_packet_prepared"] == "no"
    assert active_row["selected_interaction_route"] == SELECTED_INTERACTION_ROUTE
    assert active_row["action_block_statement"] == ACTION_BLOCK_STATEMENT
    assert active_row["A_variation_result_derived"] == "no"
    assert active_row["J_nu_derived"] == "no"
    assert active_row["sourced_maxwell_equation_derived"] == "no"
    assert active_row["matter_gauge_exchange_proved"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_psi_a_u1_action_block_definition_result_review_lean_and_surface_mirrors() -> None:
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
        "ToeNativePsiAU1InteractionActionBlockDefinitionResultReview",
        NEXT_TARGET,
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_toe_native_psi_A_u1_current_derivation_from_A_variation_packet",
        "PREVIOUS_LIVE_NEXT_TARGET_v0: "
        "review_toe_native_psi_A_u1_interaction_action_block_definition_packet_result",
        ACTION_BLOCK_STATEMENT,
        COVARIANT_DERIVATIVE_POLICY,
        FIELD_STRENGTH_POLICY,
        GAUGE_TRANSFORMATION_POLICY,
        GAUGE_COVARIANT_DERIVATIVE_TRANSFORM,
        MATTER_BLOCK_EXPANSION,
        INTERACTION_TERM_SHAPE,
        "no A-variation result",
        "no J^nu derivation",
        "no sourced Maxwell derivation",
        "no exchange proof",
        "no C_exchange closeout",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no master-action promotion",
        "full ToeFormal aggregate is recorded as NOT_RUN",
    ]:
        assert token in joined


def test_psi_a_u1_action_block_definition_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_psi_a_u1_interaction_action_block_definition_result_review_gate.py"
    )
