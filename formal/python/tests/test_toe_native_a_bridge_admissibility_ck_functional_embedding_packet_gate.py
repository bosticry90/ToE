from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.toe_native_a_bridge_admissibility_ck_constraint_candidate_packet_result_review_report import (
    DEFAULT_OUT as CANDIDATE_REVIEW_PATH,
    OUTCOME_ID as CANDIDATE_REVIEW_OUTCOME,
)
from formal.python.tools.toe_native_a_bridge_admissibility_ck_functional_embedding_packet_report import (
    ADMISSIBILITY_ONLY_ROUTE_ID,
    ARTIFACT_ID,
    A_BRIDGE_CANDIDATE_ID,
    A_BRIDGE_CONSTRAINT_EQUATION,
    A_BRIDGE_CONSTRAINT_FORM,
    A_BRIDGE_FIELD_EQUATION_MATCH,
    A_BRIDGE_SOURCE_RESIDUAL_MATCH,
    A_BRIDGE_STRESS_ENERGY_MATCH,
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    COMPONENT_PAIRING_REQUIREMENTS,
    CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    LAGRANGE_MULTIPLIER_ACTION_FORM,
    LAGRANGE_MULTIPLIER_ROUTE_ID,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PACKET_RESULT,
    PENALTY_ACTION_FORM,
    PENALTY_ROUTE_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    SELECTED_A_CK_CONSTRAINT_FAMILY,
    SELECTED_A_CK_OPTION_CLASS,
    build_toe_native_a_bridge_admissibility_ck_functional_embedding_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_a_bridge_admissibility_ck_functional_embedding_packet_report.py"
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
        if row.get("workstream_id") == workstream_id:
            return row
    raise AssertionError(f"Missing workstream: {workstream_id}")


def test_a_bridge_ck_functional_embedding_files_exist() -> None:
    for path in [
        CANDIDATE_REVIEW_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_a_bridge_ck_functional_embedding_records_routes() -> None:
    review = _json(CANDIDATE_REVIEW_PATH)
    packet = _json(DEFAULT_OUT)
    assert review["outcome_id"] == CANDIDATE_REVIEW_OUTCOME
    assert packet["artifact_id"] == ARTIFACT_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_result"] == PACKET_RESULT
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["selected_A_ck_option_class"] == SELECTED_A_CK_OPTION_CLASS
    assert packet["selected_A_ck_constraint_family"] == SELECTED_A_CK_CONSTRAINT_FAMILY
    assert packet["A_bridge_candidate_id"] == A_BRIDGE_CANDIDATE_ID
    assert packet["A_bridge_constraint_form"] == A_BRIDGE_CONSTRAINT_FORM
    assert packet["A_bridge_constraint_equation"] == A_BRIDGE_CONSTRAINT_EQUATION
    assert packet["A_bridge_field_equation_match"] == A_BRIDGE_FIELD_EQUATION_MATCH
    assert packet["A_bridge_stress_energy_match"] == A_BRIDGE_STRESS_ENERGY_MATCH
    assert packet["A_bridge_source_residual_match"] == A_BRIDGE_SOURCE_RESIDUAL_MATCH
    assert (
        packet["bridge_admissibility_constraint_form"]
        == BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert packet["lagrange_multiplier_action_form"] == LAGRANGE_MULTIPLIER_ACTION_FORM
    assert packet["penalty_action_form"] == PENALTY_ACTION_FORM
    assert (
        build_toe_native_a_bridge_admissibility_ck_functional_embedding_packet()
        == packet
    )


def test_a_bridge_ck_functional_embedding_route_statuses() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["embedding_route_count"] == 3
    routes = {row["route_id"]: row for row in packet["embedding_routes"]}
    assert routes[ADMISSIBILITY_ONLY_ROUTE_ID]["status"] == (
        "selected_non_dynamical_route_consistency_rule"
    )
    assert routes[ADMISSIBILITY_ONLY_ROUTE_ID]["selected_for_current_packet"] is True
    assert routes[LAGRANGE_MULTIPLIER_ROUTE_ID]["status"] == (
        "blocked_by_component_pairing_multiplier_domain_covariance_boundary_"
        "variation_and_gauge_dynamics_scope"
    )
    assert routes[LAGRANGE_MULTIPLIER_ROUTE_ID]["blocking_reasons"] == (
        COMPONENT_PAIRING_REQUIREMENTS
    )
    assert routes[PENALTY_ROUTE_ID]["status"] == "recorded_unlicensed_dynamical_penalty"
    assert "no norm over the heterogeneous route tuple is defined" in routes[
        PENALTY_ROUTE_ID
    ]["blocking_reasons"]
    assert packet["selected_embedding_route_id"] == ADMISSIBILITY_ONLY_ROUTE_ID
    assert packet["review_row_count"] == 12
    assert packet["review_row_accepted_count"] == 12


def test_a_bridge_ck_functional_embedding_blocks_action_and_closure_claims() -> None:
    packet = _json(DEFAULT_OUT)
    for key in [
        "functional_embedding_packet_prepared",
        "functional_embedding_options_recorded",
        "admissibility_only_route_selected",
        "constraint_as_admissibility_rule_selected",
        "lagrange_multiplier_route_recorded",
        "lagrange_multiplier_route_blocked",
        "penalty_route_recorded",
        "penalty_route_unlicensed",
        "route_consistency_tuple_carried_forward",
        "field_equation_match_component_preserved",
        "stress_energy_match_component_preserved",
        "source_residual_match_component_preserved",
    ]:
        assert packet[key] is True, key
    for key in [
        "bridge_proof_claimed",
        "bridge_admissibility_proved",
        "route_consistency_tuple_proved",
        "dynamical_action_embedding_selected",
        "constraint_as_action_term_selected",
        "component_pairing_rule_selected",
        "multiplier_domain_selected",
        "covariance_control_established",
        "boundary_term_policy_selected",
        "boundary_terms_controlled",
        "variation_policy_selected",
        "gauge_dynamics_preservation_proved",
        "heterogeneous_tuple_norm_defined",
        "penalty_route_licensed",
        "C_k_action_embedding_constructed",
        "C_k_variation_executed",
        "lambda_variation_executed",
        "A_variation_of_candidate_executed",
        "metric_variation_of_candidate_executed",
        "J_nu_derived",
        "psi_current_route_constructed",
        "external_current_native_derivation_selected",
        "sourced_maxwell_equation_derived",
        "matter_current_exchange_route_proved",
        "full_em_closure_claimed",
        "qft_gr_closure_claimed",
        "semiclassical_coupling_authorized",
        "empirical_validation_claimed",
        "master_action_promoted",
    ]:
        assert packet[key] is False, key
    for phrase in [
        "selects the admissibility-only route C_bridge^A = 0",
        "does not functionalize C_bridge^A",
        "does not embed it in S_C",
        "does not select Lambda_bridge or a multiplier domain",
        "does not select a component pairing rule",
        "does not prove covariance control",
        "does not select a boundary-term policy",
        "does not select a variation policy",
        "does not prove preservation of the intended gauge dynamics",
        "does not license the penalty route",
        "does not define a norm over the heterogeneous route tuple",
        "does not execute C_k variation",
        "does not derive J^nu",
        "does not derive sourced Maxwell",
        "does not close EM",
        "does not close QFT-GR",
        "does not promote the master action",
    ]:
        assert phrase in packet["non_claim_boundary"], phrase


def test_a_bridge_ck_functional_embedding_validation_policy_not_run() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False
    assert policy["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"


def test_a_bridge_ck_functional_embedding_rotates_to_review_target() -> None:
    registry = _json(REGISTRY_PATH)
    skip_if_not_current_target(registry, NEXT_TARGET)
    state = registry["current_target_state"]
    active = [row for row in registry["workstreams"] if row.get("status") == "active"]
    assert len(active) == 1
    assert state["previous_live_next_target"] == CONSUMED_TARGET
    assert state["live_next_target"] == NEXT_TARGET
    assert state["active_lane"] == NEXT_TARGET
    assert state["live_next_target_evidence"] == (
        "formal/toe_formal/ToeFormal/Derivation/"
        "ToeNativeABridgeAdmissibilityCKFunctionalEmbeddingPacket.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_"
        "20260622_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["packet_result"] == PACKET_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["admissibility_only_route_selected"] == "yes"
    assert consumed["lagrange_multiplier_route_blocked"] == "yes"
    assert consumed["penalty_route_licensed"] == "no"
    assert consumed["heterogeneous_tuple_norm_defined"] == "no"
    assert consumed["C_k_action_embedding_constructed"] == "no"
    assert consumed["C_k_variation_executed"] == "no"
    assert consumed["J_nu_derived"] == "no"
    assert consumed["sourced_maxwell_equation_derived"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["outcome_id"] == OUTCOME_ID
    assert active_row["packet_result"] == PACKET_RESULT
    assert active_row["review_prepared"] == "no"
    assert active_row["review_result"] == "PENDING"
    assert active_row["admissibility_only_route_selected"] == "yes"
    assert active_row["constraint_as_action_term_selected"] == "no"
    assert active_row["component_pairing_rule_selected"] == "no"
    assert active_row["multiplier_domain_selected"] == "no"
    assert active_row["covariance_control_established"] == "no"
    assert active_row["boundary_term_policy_selected"] == "no"
    assert active_row["variation_policy_selected"] == "no"
    assert active_row["gauge_dynamics_preservation_proved"] == "no"
    assert active_row["heterogeneous_tuple_norm_defined"] == "no"
    assert active_row["penalty_route_licensed"] == "no"
    assert active_row["C_k_action_embedding_constructed"] == "no"
    assert active_row["C_k_variation_executed"] == "no"
    assert active_row["J_nu_derived"] == "no"
    assert active_row["sourced_maxwell_equation_derived"] == "no"
    assert active_row["matter_current_exchange_route_proved"] == "no"
    assert active_row["full_em_closure_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_a_bridge_ck_functional_embedding_mirrors() -> None:
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
        PACKET_RESULT,
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        "ToeNativeABridgeAdmissibilityCKFunctionalEmbeddingPacket",
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "review_toe_native_A_bridge_admissibility_ck_functional_embedding_packet_result",
        A_BRIDGE_CANDIDATE_ID,
        A_BRIDGE_CONSTRAINT_FORM,
        A_BRIDGE_CONSTRAINT_EQUATION,
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        LAGRANGE_MULTIPLIER_ACTION_FORM,
        PENALTY_ACTION_FORM,
        "selects the admissibility-only route C_bridge^A = 0",
        "does not functionalize C_bridge^A",
        "does not embed it in S_C",
        "does not derive J^nu",
        "does not derive sourced Maxwell",
        "does not close EM",
        "does not close QFT-GR",
        "master-action promotion remains blocked",
        "NOT_RUN",
    ]:
        assert token in joined


def test_a_bridge_ck_functional_embedding_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_a_bridge_admissibility_ck_functional_embedding_packet_gate.py"
    )
