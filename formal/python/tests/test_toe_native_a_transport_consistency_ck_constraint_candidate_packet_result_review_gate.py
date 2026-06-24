from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.toe_native_a_transport_consistency_ck_constraint_candidate_packet_report import (
    DEFAULT_OUT as CANDIDATE_PACKET_PATH,
    OUTCOME_ID as CANDIDATE_PACKET_OUTCOME,
    PACKET_RESULT as CANDIDATE_PACKET_RESULT,
)
from formal.python.tools.toe_native_a_transport_consistency_ck_constraint_candidate_packet_result_review_report import (
    A_BRIDGE_CONSTRAINT_EQUATION,
    A_BRIDGE_CONSTRAINT_FORM,
    A_BRIDGE_FIELD_EQUATION_MATCH,
    A_BRIDGE_SOURCE_RESIDUAL_MATCH,
    A_BRIDGE_STRESS_ENERGY_MATCH,
    A_FIELD_DOMAIN_POLICY,
    ARTIFACT_ID,
    CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    F_DEFINITION_POLICY,
    FULL_TOEFORMAL_STATUS,
    GAUGE_GROUP_POLICY,
    KNOWN_A_TRANSPORT_CHAIN_FORM,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PACKET_RESULT,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    REVIEW_RESULT,
    SCHEMA_ID,
    SELECTED_A_CK_CONSTRAINT_FAMILY,
    SELECTED_A_CK_OPTION_CLASS,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    SOURCE_ROUTE_STILL_BLOCKED,
    TRANSPORT_CANDIDATE_ID,
    TRANSPORT_CANDIDATE_TYPE,
    TRANSPORT_CONSTRAINT_EQUATION,
    TRANSPORT_CONSTRAINT_FORM,
    TRANSPORT_RULE_CLASSIFICATION,
    TRANSPORT_RULE_EPISTEMIC_STATUS,
    VACUUM_EULER_LAGRANGE_ROUTE,
    build_toe_native_a_transport_consistency_ck_constraint_candidate_packet_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_a_transport_consistency_ck_constraint_candidate_packet_result_review_report.py"
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


def test_a_transport_ck_candidate_review_files_exist() -> None:
    for path in [
        CANDIDATE_PACKET_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_a_transport_ck_candidate_review_accepts_candidate() -> None:
    packet = _json(CANDIDATE_PACKET_PATH)
    review = _json(DEFAULT_OUT)
    assert packet["outcome_id"] == CANDIDATE_PACKET_OUTCOME
    assert packet["packet_result"] == CANDIDATE_PACKET_RESULT
    assert review["artifact_id"] == ARTIFACT_ID
    assert review["schema_id"] == SCHEMA_ID
    assert review["packet_id"] == PACKET_ID
    assert review["prepared"] is True
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["packet_result"] == PACKET_RESULT
    assert review["review_result"] == REVIEW_RESULT
    assert review["packet_classification"] == PACKET_CLASSIFICATION
    assert review["consumed_target"] == CONSUMED_TARGET
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["candidate_packet_outcome"] == CANDIDATE_PACKET_OUTCOME
    assert review["candidate_packet_result"] == CANDIDATE_PACKET_RESULT
    assert (
        build_toe_native_a_transport_consistency_ck_constraint_candidate_packet_result_review()
        == review
    )


def test_a_transport_ck_candidate_review_preserves_transport_rule() -> None:
    review = _json(DEFAULT_OUT)
    assert review["selected_A_ck_option_class"] == SELECTED_A_CK_OPTION_CLASS
    assert review["selected_A_ck_constraint_family"] == SELECTED_A_CK_CONSTRAINT_FAMILY
    assert review["transport_candidate_id"] == TRANSPORT_CANDIDATE_ID
    assert review["transport_candidate_type"] == TRANSPORT_CANDIDATE_TYPE
    assert review["transport_rule_classification"] == TRANSPORT_RULE_CLASSIFICATION
    assert review["transport_rule_epistemic_status"] == TRANSPORT_RULE_EPISTEMIC_STATUS
    assert review["transport_constraint_form"] == TRANSPORT_CONSTRAINT_FORM
    assert review["transport_constraint_equation"] == TRANSPORT_CONSTRAINT_EQUATION
    assert review["transport_admissibility_constraint_form"] == (
        TRANSPORT_CONSTRAINT_EQUATION
    )
    assert review["known_A_transport_chain_form"] == KNOWN_A_TRANSPORT_CHAIN_FORM
    assert review["review_accepts_vacuum_u1_derivation_chain_stability_candidate"] is True
    assert review["derivation_chain_stability_candidate_accepted"] is True
    assert review["transport_constraint_preserved"] is True
    assert review["transport_tuple_preserved"] is True
    assert review["transport_components_preserved"] is True
    assert review["transport_components_proved"] is False
    assert review["transport_candidate_classified_as_admissibility_only"] is True


def test_a_transport_ck_candidate_review_preserves_context() -> None:
    review = _json(DEFAULT_OUT)
    assert review["source_candidate_constraint_id"] == SOURCE_CANDIDATE_CONSTRAINT_ID
    assert review["source_candidate_constraint_form"] == SOURCE_CANDIDATE_CONSTRAINT_FORM
    assert (
        review["source_admissibility_constraint_form"]
        == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert review["A_bridge_constraint_form"] == A_BRIDGE_CONSTRAINT_FORM
    assert review["A_bridge_constraint_equation"] == A_BRIDGE_CONSTRAINT_EQUATION
    assert review["bridge_admissibility_constraint_form"] == (
        A_BRIDGE_CONSTRAINT_EQUATION
    )
    assert review["A_bridge_field_equation_match"] == A_BRIDGE_FIELD_EQUATION_MATCH
    assert review["A_bridge_stress_energy_match"] == A_BRIDGE_STRESS_ENERGY_MATCH
    assert review["A_bridge_source_residual_match"] == A_BRIDGE_SOURCE_RESIDUAL_MATCH
    assert review["gauge_group_policy"] == GAUGE_GROUP_POLICY
    assert review["A_field_domain_policy"] == A_FIELD_DOMAIN_POLICY
    assert review["F_definition_policy"] == F_DEFINITION_POLICY
    assert review["vacuum_euler_lagrange_route"] == VACUUM_EULER_LAGRANGE_ROUTE
    assert review["on_shell_vacuum_conservation_identity"] == (
        ON_SHELL_VACUUM_CONSERVATION_IDENTITY
    )
    assert review["source_route_still_blocked"] == SOURCE_ROUTE_STILL_BLOCKED
    assert review["source_and_bridge_context_retained"] is True
    assert review["vacuum_u1_scope_preserved"] is True
    assert review["known_A_chain_retained"] is True
    assert review["closed_A_ck_rule_roles"] == [
        "source admissibility",
        "bridge admissibility",
        "transport consistency",
    ]
    assert review["closed_A_ck_rule_family_count_after_review"] == 3


def test_a_transport_ck_candidate_review_accepts_required_points() -> None:
    review = _json(DEFAULT_OUT)
    assert review["review_criteria_count"] == 14
    assert review["review_criteria_accepted_count"] == 14
    assert {row["row_id"] for row in review["review_criteria"]} == {
        "transport_candidate_review_target_consumed",
        "C_transport_A_tuple_preserved_exactly",
        "C_transport_A_equation_preserved_exactly",
        "transport_components_preserved_unproved",
        "vacuum_u1_scope_preserved",
        "source_and_bridge_rules_retained_as_context",
        "known_A_chain_retained",
        "admissibility_only_classification_preserved",
        "no_transport_proof_or_concrete_functional",
        "no_ck_action_embedding_or_variation",
        "no_current_sourced_maxwell_or_exchange_route",
        "no_closure_coupling_validation_phase_or_promotion",
        "full_toeformal_aggregate_recorded_not_run",
        "functional_embedding_packet_selected",
    }


def test_a_transport_ck_candidate_review_blocks_shortcuts() -> None:
    review = _json(DEFAULT_OUT)
    assert review["functional_embedding_packet_authorized"] is True
    assert review["functional_embedding_packet_prepared"] is False
    assert review["multiplier_action_route_test_authorized"] is True
    assert review["penalty_route_test_authorized"] is True
    assert review["direct_dynamical_law_interpretation_test_authorized"] is True
    for key in [
        "functional_embedding_executed",
        "multiplier_action_route_selected",
        "penalty_route_selected",
        "direct_dynamical_law_interpretation_selected",
        "transport_candidate_functional_defined",
        "transport_candidate_functional_selected",
        "transport_candidate_recorded_as_action_term",
        "transport_candidate_recorded_as_new_dynamical_law",
        "transport_candidate_rule_proved",
        "transport_consistency_claimed",
        "transport_consistency_proved",
        "transport_proof_claimed",
        "full_route_alignment_proof_claimed",
        "full_route_alignment_proved",
        "route_chain_compatibility_proved",
        "source_admissibility_proved",
        "source_conservation_proved",
        "bridge_admissibility_proved",
        "bridge_route_alignment_verified",
        "route_consistency_tuple_proved",
        "new_conservation_proof_claimed",
        "new_source_admissibility_proof_claimed",
        "concrete_ck_functional_selected",
        "concrete_ck_functional_defined",
        "fully_concrete_ck_functional_selected",
        "fully_concrete_ck_functional_defined",
        "ck_action_embedding_claimed",
        "ck_action_embedding_constructed",
        "C_k_action_embedding_constructed",
        "candidate_action_insertion_executed",
        "constraint_as_action_term_selected",
        "constraint_term_selected",
        "ck_variation_executed",
        "C_k_variation_executed",
        "lambda_variation_executed",
        "metric_variation_of_candidate_executed",
        "A_variation_of_candidate_executed",
        "current_route_derived",
        "current_source_route_constructed",
        "matter_current_J_nu_derived",
        "J_nu_derived",
        "psi_current_route_constructed",
        "external_current_native_derivation_selected",
        "matter_current_exchange_route_proved",
        "matter_gauge_energy_exchange_proved",
        "sourced_maxwell_equation_derived",
        "sourced_maxwell_route_derived",
        "full_em_closure_claimed",
        "em_closure_claimed",
        "qft_gr_closure_claimed",
        "qft_gr_solved",
        "qft_gr_seam_closed",
        "semiclassical_coupling_authorized",
        "semiclassical_coupling_claimed",
        "semiclassical_einstein_equation_derived",
        "master_action_promoted",
        "master_action_promotion_authorized",
        "canonical_master_action_promoted",
        "empirical_validation_claimed",
        "public_readiness_claimed",
        "phase2_readiness_claim",
        "pillar_completion_inferred",
        "seam_closure_claim",
    ]:
        assert review[key] is False, key
    for phrase in [
        "accepts C_transport^A = 0 only as an admissibility-only vacuum U(1)",
        "does not define a fully concrete C_transport^A functional",
        "does not embed C_transport^A into the action",
        "does not define a C_k action term",
        "does not select a multiplier/action route",
        "does not select a penalty route",
        "does not execute C_k variation",
        "does not prove transport consistency",
        "does not prove full route alignment",
        "does not derive J^nu",
        "does not derive sourced Maxwell",
        "does not close EM",
        "does not close QFT-GR",
        "does not authorize Phase 2",
        "records no Phase 2 authorization",
        "does not promote the master action",
        "NOT_RUN",
    ]:
        assert phrase in review["non_claim_boundary"], phrase


def test_a_transport_ck_candidate_review_validation_policy_not_run() -> None:
    review = _json(DEFAULT_OUT)
    policy = review["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == FULL_TOEFORMAL_STATUS
    assert policy["aggregate_lean_validation_status_allowed_values"] == ["NOT_RUN"]
    assert policy["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert policy["full_toeformal_aggregate_passed"] is False
    assert policy["full_toeformal_aggregate_failed"] is False
    assert policy["full_toeformal_aggregate_timed_out"] is False
    assert review["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert review["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"
    assert review["full_toeformal_aggregate_passed"] is False
    assert review["full_toeformal_aggregate_failed"] is False
    assert review["full_toeformal_aggregate_timed_out"] is False


def test_a_transport_ck_candidate_review_rotates_to_embedding_target() -> None:
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
        "ToeNativeATransportConsistencyCKConstraintCandidatePacketResultReview.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_PACKET_"
        "RESULT_REVIEW_20260623_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["transport_candidate_id"] == TRANSPORT_CANDIDATE_ID
    assert consumed["transport_constraint_equation"] == TRANSPORT_CONSTRAINT_EQUATION
    assert consumed["review_accepts_vacuum_u1_derivation_chain_stability_candidate"] == "yes"
    assert consumed["functional_embedding_packet_authorized"] == "yes"
    assert consumed["functional_embedding_packet_prepared"] == "no"
    assert consumed["transport_candidate_functional_defined"] == "no"
    assert consumed["C_k_variation_executed"] == "no"
    assert consumed["J_nu_derived"] == "no"
    assert consumed["sourced_maxwell_equation_derived"] == "no"
    assert consumed["full_em_closure_claimed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["review_result"] == OUTCOME_ID
    assert active_row["functional_embedding_packet_authorized"] == "yes"
    assert active_row["functional_embedding_packet_prepared"] == "no"
    assert active_row["multiplier_action_route_test_authorized"] == "yes"
    assert active_row["penalty_route_test_authorized"] == "yes"
    assert active_row["direct_dynamical_law_interpretation_test_authorized"] == "yes"
    assert active_row["multiplier_action_route_selected"] == "no"
    assert active_row["penalty_route_selected"] == "no"
    assert active_row["direct_dynamical_law_interpretation_selected"] == "no"
    assert active_row["transport_candidate_functional_defined"] == "no"
    assert active_row["C_k_action_embedding_constructed"] == "no"
    assert active_row["C_k_variation_executed"] == "no"
    assert active_row["J_nu_derived"] == "no"
    assert active_row["sourced_maxwell_equation_derived"] == "no"
    assert active_row["full_em_closure_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_a_transport_ck_candidate_review_mirrors() -> None:
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
        CONSUMED_TARGET,
        NEXT_TARGET,
        "ToeNativeATransportConsistencyCKConstraintCandidatePacketResultReview",
        (
            "CURRENT_LIVE_NEXT_TARGET_v0: "
            "prepare_toe_native_A_transport_consistency_ck_functional_embedding_packet"
        ),
        TRANSPORT_CANDIDATE_ID,
        TRANSPORT_CONSTRAINT_FORM,
        TRANSPORT_CONSTRAINT_EQUATION,
        SOURCE_CANDIDATE_CONSTRAINT_FORM,
        SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        A_BRIDGE_CONSTRAINT_FORM,
        A_BRIDGE_CONSTRAINT_EQUATION,
        "admissibility-only vacuum U(1) derivation-chain stability candidate",
        "does not define a fully concrete C_transport^A functional",
        "does not embed C_transport^A into the action",
        "does not execute C_k variation",
        "does not prove transport consistency",
        "does not derive J^nu",
        "does not derive sourced Maxwell",
        "does not close EM",
        "does not close QFT-GR",
        "does not promote the master action",
        "NOT_RUN",
    ]:
        assert token in joined


def test_a_transport_ck_candidate_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_a_transport_consistency_ck_constraint_candidate_packet_result_review_gate.py"
    )
