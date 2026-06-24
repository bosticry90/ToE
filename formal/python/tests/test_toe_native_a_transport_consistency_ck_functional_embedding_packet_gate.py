from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.toe_native_a_transport_consistency_ck_constraint_candidate_packet_result_review_report import (
    DEFAULT_OUT as CANDIDATE_REVIEW_PATH,
    OUTCOME_ID as CANDIDATE_REVIEW_OUTCOME,
)
from formal.python.tools.toe_native_a_transport_consistency_ck_functional_embedding_packet_report import (
    ADMISSIBILITY_ONLY_ROUTE_ID,
    ARTIFACT_ID,
    A_BRIDGE_CONSTRAINT_EQUATION,
    A_BRIDGE_CONSTRAINT_FORM,
    A_BRIDGE_FIELD_EQUATION_MATCH,
    A_BRIDGE_SOURCE_RESIDUAL_MATCH,
    A_BRIDGE_STRESS_ENERGY_MATCH,
    CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    DIRECT_DYNAMICAL_LAW_INTERPRETATION_ID,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
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
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    TRANSPORT_ACTION_EMBEDDING_CHAIN_FORM,
    TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
    TRANSPORT_CANDIDATE_ID,
    TRANSPORT_CANDIDATE_TYPE,
    TRANSPORT_CONSTRAINT_EQUATION,
    TRANSPORT_CONSTRAINT_FORM,
    TRANSPORT_MULTIPLIER_BLOCKING_REASONS,
    TRANSPORT_PENALTY_BLOCKING_REASONS,
    TRANSPORT_RULE_CLASSIFICATION,
    build_toe_native_a_transport_consistency_ck_functional_embedding_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_a_transport_consistency_ck_functional_embedding_packet_report.py"
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


def test_a_transport_ck_functional_embedding_files_exist() -> None:
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


def test_a_transport_ck_functional_embedding_records_routes() -> None:
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
    assert packet["transport_candidate_id"] == TRANSPORT_CANDIDATE_ID
    assert packet["transport_candidate_type"] == TRANSPORT_CANDIDATE_TYPE
    assert packet["transport_rule_classification"] == TRANSPORT_RULE_CLASSIFICATION
    assert packet["transport_constraint_form"] == TRANSPORT_CONSTRAINT_FORM
    assert packet["transport_constraint_equation"] == TRANSPORT_CONSTRAINT_EQUATION
    assert (
        packet["transport_admissibility_constraint_form"]
        == TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert packet["transport_action_embedding_chain_form"] == (
        TRANSPORT_ACTION_EMBEDDING_CHAIN_FORM
    )
    assert packet["source_candidate_constraint_id"] == SOURCE_CANDIDATE_CONSTRAINT_ID
    assert packet["source_candidate_constraint_form"] == SOURCE_CANDIDATE_CONSTRAINT_FORM
    assert packet["source_admissibility_constraint_form"] == (
        SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert packet["A_bridge_constraint_form"] == A_BRIDGE_CONSTRAINT_FORM
    assert packet["A_bridge_constraint_equation"] == A_BRIDGE_CONSTRAINT_EQUATION
    assert packet["A_bridge_field_equation_match"] == A_BRIDGE_FIELD_EQUATION_MATCH
    assert packet["A_bridge_stress_energy_match"] == A_BRIDGE_STRESS_ENERGY_MATCH
    assert packet["A_bridge_source_residual_match"] == A_BRIDGE_SOURCE_RESIDUAL_MATCH
    assert packet["lagrange_multiplier_action_form"] == LAGRANGE_MULTIPLIER_ACTION_FORM
    assert packet["penalty_action_form"] == PENALTY_ACTION_FORM
    assert (
        build_toe_native_a_transport_consistency_ck_functional_embedding_packet()
        == packet
    )


def test_a_transport_ck_functional_embedding_route_statuses() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["embedding_route_count"] == 3
    routes = {row["route_id"]: row for row in packet["embedding_routes"]}
    assert routes[ADMISSIBILITY_ONLY_ROUTE_ID]["status"] == (
        "selected_non_dynamical_vacuum_u1_derivation_chain_stability_rule"
    )
    assert routes[ADMISSIBILITY_ONLY_ROUTE_ID]["selected_for_current_packet"] is True
    assert routes[ADMISSIBILITY_ONLY_ROUTE_ID]["action_term_selected"] is False
    assert routes[LAGRANGE_MULTIPLIER_ROUTE_ID]["status"] == (
        "blocked_by_route_component_domain_pairing_covariance_boundary_regime_"
        "projection_and_variation_scope"
    )
    assert routes[LAGRANGE_MULTIPLIER_ROUTE_ID]["selected_for_current_packet"] is False
    assert routes[LAGRANGE_MULTIPLIER_ROUTE_ID]["blocking_reasons"] == (
        TRANSPORT_MULTIPLIER_BLOCKING_REASONS
    )
    assert routes[PENALTY_ROUTE_ID]["status"] == "recorded_not_licensed"
    assert routes[PENALTY_ROUTE_ID]["selected_for_current_packet"] is False
    assert routes[PENALTY_ROUTE_ID]["blocking_reasons"] == (
        TRANSPORT_PENALTY_BLOCKING_REASONS
    )
    assert packet["direct_dynamical_law_interpretation_id"] == (
        DIRECT_DYNAMICAL_LAW_INTERPRETATION_ID
    )
    assert packet["direct_dynamical_law_interpretation_recorded"] is True
    assert packet["direct_dynamical_law_interpretation_blocked"] is True
    assert packet["direct_dynamical_law_interpretation_selected"] is False
    assert packet["selected_embedding_route_id"] == ADMISSIBILITY_ONLY_ROUTE_ID
    assert packet["review_row_count"] == 12
    assert packet["review_row_accepted_count"] == 12


def test_a_transport_ck_functional_embedding_blocks_action_current_and_closure() -> None:
    packet = _json(DEFAULT_OUT)
    for key in [
        "functional_embedding_packet_prepared",
        "functional_embedding_options_recorded",
        "admissibility_only_route_selected",
        "constraint_as_admissibility_rule_selected",
        "lagrange_multiplier_route_recorded",
        "lagrange_multiplier_route_blocked",
        "penalty_route_recorded",
        "missing_multiplier_type",
        "component_pairing_rule_missing",
        "transport_map_domains_codomains_missing",
        "covariance_rule_missing",
        "boundary_regime_projection_control_missing",
        "embedding_variation_policy_missing",
        "penalty_would_change_dynamics",
        "direct_dynamical_law_interpretation_recorded",
        "direct_dynamical_law_interpretation_blocked",
        "transport_tuple_carried_forward",
        "source_and_bridge_context_preserved",
        "vacuum_u1_scope_preserved",
    ]:
        assert packet[key] is True, key
    for key in [
        "dynamical_action_embedding_selected",
        "constraint_as_action_term_selected",
        "transport_candidate_recorded_as_action_term",
        "transport_candidate_recorded_as_new_dynamical_law",
        "transport_functional_selected",
        "transport_candidate_functional_defined",
        "transport_candidate_functional_selected",
        "component_pairing_rule_selected",
        "transport_map_domains_codomains_selected",
        "constraint_multiplier_type_selected",
        "constraint_term_selected",
        "multiplier_type_selected",
        "multiplier_domain_selected",
        "covariance_of_multiplier_pairing_established",
        "boundary_terms_controlled",
        "boundary_regime_projection_controlled",
        "variation_policy_for_embedding_selected",
        "penalty_route_licensed",
        "heterogeneous_tuple_norm_defined",
        "fully_concrete_ck_functional_selected",
        "fully_concrete_ck_functional_defined",
        "concrete_ck_functional_selected",
        "concrete_ck_functional_defined",
        "C_k_action_embedding_constructed",
        "candidate_action_insertion_executed",
        "C_k_variation_executed",
        "lambda_variation_executed",
        "metric_variation_of_candidate_executed",
        "A_variation_of_candidate_executed",
        "penalty_variation_executed",
        "transport_consistency_proved",
        "transport_proof_claimed",
        "transport_components_proved",
        "full_route_alignment_proved",
        "route_chain_compatibility_proved",
        "source_admissibility_proved",
        "bridge_admissibility_proved",
        "J_nu_derived",
        "psi_current_route_constructed",
        "external_current_native_derivation_selected",
        "sourced_maxwell_equation_derived",
        "matter_current_exchange_route_proved",
        "full_em_closure_claimed",
        "qft_gr_closure_claimed",
        "semiclassical_coupling_authorized",
        "empirical_validation_claimed",
        "phase2_readiness_claim",
        "master_action_promoted",
    ]:
        assert packet[key] is False, key
    for phrase in [
        "selects the admissibility-only route C_transport^A = 0",
        "does not functionalize C_transport^A",
        "does not embed C_transport^A into the action",
        "does not define a C_k action term",
        "does not select Lambda_transport",
        "does not select transport-map domains/codomains",
        "does not license the penalty route",
        "does not interpret the candidate as a direct dynamical law",
        "does not prove transport consistency",
        "does not derive J^nu",
        "does not derive sourced Maxwell",
        "does not close EM",
        "does not close QFT-GR",
        "does not authorize Phase 2",
        "does not promote the master action",
        "NOT_RUN",
    ]:
        assert phrase in packet["non_claim_boundary"], phrase


def test_a_transport_ck_functional_embedding_validation_policy() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == (
        FULL_TOEFORMAL_AGGREGATE_STATUS
    )
    assert policy["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert policy["full_toeformal_aggregate_passed"] is False
    assert policy["full_toeformal_aggregate_failed"] is False
    assert policy["full_toeformal_aggregate_timed_out"] is False
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_a_transport_ck_functional_embedding_rotates_to_review_target() -> None:
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
        "ToeNativeATransportConsistencyCKFunctionalEmbeddingPacket.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_PACKET_"
        "20260623_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["packet_result"] == PACKET_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["transport_constraint_equation"] == TRANSPORT_CONSTRAINT_EQUATION
    assert consumed["admissibility_only_route_selected"] == "yes"
    assert consumed["lagrange_multiplier_route_blocked"] == "yes"
    assert consumed["penalty_route_licensed"] == "no"
    assert consumed["direct_dynamical_law_interpretation_blocked"] == "yes"
    assert consumed["constraint_as_action_term_selected"] == "no"
    assert consumed["transport_map_domains_codomains_selected"] == "no"
    assert consumed["C_k_variation_executed"] == "no"
    assert consumed["J_nu_derived"] == "no"
    assert consumed["sourced_maxwell_equation_derived"] == "no"
    assert consumed["transport_consistency_proved"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["outcome_id"] == OUTCOME_ID
    assert active_row["packet_result"] == PACKET_RESULT
    assert active_row["transport_constraint_equation"] == TRANSPORT_CONSTRAINT_EQUATION
    assert active_row["admissibility_only_route_selected"] == "yes"
    assert active_row["review_prepared"] == "no"
    assert active_row["constraint_as_action_term_selected"] == "no"
    assert active_row["component_pairing_rule_selected"] == "no"
    assert active_row["transport_map_domains_codomains_selected"] == "no"
    assert active_row["covariance_of_multiplier_pairing_established"] == "no"
    assert active_row["boundary_regime_projection_controlled"] == "no"
    assert active_row["penalty_route_licensed"] == "no"
    assert active_row["direct_dynamical_law_interpretation_selected"] == "no"
    assert active_row["C_k_variation_executed"] == "no"
    assert active_row["transport_consistency_proved"] == "no"
    assert active_row["J_nu_derived"] == "no"
    assert active_row["full_em_closure_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["phase2_readiness_claim"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_a_transport_ck_functional_embedding_mirrors() -> None:
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
        "ToeNativeATransportConsistencyCKFunctionalEmbeddingPacket",
        (
            "CURRENT_LIVE_NEXT_TARGET_v0: "
            "review_toe_native_A_transport_consistency_ck_functional_embedding_packet_result"
        ),
        TRANSPORT_CANDIDATE_ID,
        TRANSPORT_CONSTRAINT_FORM,
        TRANSPORT_CONSTRAINT_EQUATION,
        ADMISSIBILITY_ONLY_ROUTE_ID,
        LAGRANGE_MULTIPLIER_ROUTE_ID,
        PENALTY_ROUTE_ID,
        DIRECT_DYNAMICAL_LAW_INTERPRETATION_ID,
        TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
        LAGRANGE_MULTIPLIER_ACTION_FORM,
        PENALTY_ACTION_FORM,
        "missing transport-map domains/codomains",
        "missing boundary/regime projection control",
        "selects the admissibility-only route C_transport^A = 0",
        "does not functionalize C_transport^A",
        "does not embed C_transport^A into the action",
        "does not define a C_k action term",
        "does not select Lambda_transport",
        "does not license the penalty route",
        "does not interpret the candidate as a direct dynamical law",
        "does not prove transport consistency",
        "no EM closure",
        "no QFT-GR closure",
        "master-action promotion remains blocked",
        "NOT_RUN",
    ]:
        assert token in joined


def test_a_transport_ck_functional_embedding_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_a_transport_consistency_ck_functional_embedding_packet_gate.py"
    )
