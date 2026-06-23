from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.toe_native_a_bridge_admissibility_ck_functional_embedding_packet_report import (
    ADMISSIBILITY_ONLY_ROUTE_ID,
    A_BRIDGE_CANDIDATE_ID,
    A_BRIDGE_CONSTRAINT_EQUATION,
    A_BRIDGE_CONSTRAINT_FORM,
    A_BRIDGE_FIELD_EQUATION_MATCH,
    A_BRIDGE_SOURCE_RESIDUAL_MATCH,
    A_BRIDGE_STRESS_ENERGY_MATCH,
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    DEFAULT_OUT as EMBEDDING_PACKET_PATH,
    LAGRANGE_MULTIPLIER_ACTION_FORM,
    LAGRANGE_MULTIPLIER_ROUTE_ID,
    OUTCOME_ID as EMBEDDING_PACKET_OUTCOME,
    PACKET_RESULT as EMBEDDING_PACKET_RESULT,
    PENALTY_ACTION_FORM,
    PENALTY_ROUTE_ID,
    SELECTED_A_CK_CONSTRAINT_FAMILY,
    SELECTED_A_CK_OPTION_CLASS,
)
from formal.python.tools.toe_native_a_bridge_admissibility_ck_functional_embedding_packet_result_review_report import (
    ARTIFACT_ID,
    CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    FIRST_A_BRIDGE_RULE_CLASSIFICATION,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    REVIEW_RESULT,
    SCHEMA_ID,
    build_toe_native_a_bridge_admissibility_ck_functional_embedding_packet_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_a_bridge_admissibility_ck_functional_embedding_packet_result_review_report.py"
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


def test_a_bridge_ck_functional_embedding_review_files_exist() -> None:
    for path in [
        EMBEDDING_PACKET_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_a_bridge_ck_functional_embedding_review_accepts_packet_result() -> None:
    packet = _json(EMBEDDING_PACKET_PATH)
    review = _json(DEFAULT_OUT)
    assert packet["outcome_id"] == EMBEDDING_PACKET_OUTCOME
    assert packet["packet_result"] == EMBEDDING_PACKET_RESULT
    assert review["artifact_id"] == ARTIFACT_ID
    assert review["schema_id"] == SCHEMA_ID
    assert review["packet_id"] == PACKET_ID
    assert review["prepared"] is True
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["packet_result"] == "REVIEW_ACCEPTED"
    assert review["review_result"] == REVIEW_RESULT
    assert review["packet_classification"] == PACKET_CLASSIFICATION
    assert review["consumed_target"] == CONSUMED_TARGET
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["embedding_packet_outcome"] == EMBEDDING_PACKET_OUTCOME
    assert review["embedding_packet_result"] == EMBEDDING_PACKET_RESULT
    assert (
        build_toe_native_a_bridge_admissibility_ck_functional_embedding_packet_result_review()
        == review
    )


def test_a_bridge_ck_functional_embedding_review_carries_route_forms() -> None:
    review = _json(DEFAULT_OUT)
    assert review["selected_A_ck_option_class"] == SELECTED_A_CK_OPTION_CLASS
    assert review["selected_A_ck_constraint_family"] == SELECTED_A_CK_CONSTRAINT_FAMILY
    assert review["A_bridge_candidate_id"] == A_BRIDGE_CANDIDATE_ID
    assert review["A_bridge_constraint_form"] == A_BRIDGE_CONSTRAINT_FORM
    assert review["A_bridge_constraint_equation"] == A_BRIDGE_CONSTRAINT_EQUATION
    assert review["A_bridge_field_equation_match"] == A_BRIDGE_FIELD_EQUATION_MATCH
    assert review["A_bridge_stress_energy_match"] == A_BRIDGE_STRESS_ENERGY_MATCH
    assert review["A_bridge_source_residual_match"] == A_BRIDGE_SOURCE_RESIDUAL_MATCH
    assert review["selected_embedding_route_id"] == ADMISSIBILITY_ONLY_ROUTE_ID
    assert (
        review["bridge_admissibility_constraint_form"]
        == BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert review["lagrange_multiplier_route_id"] == LAGRANGE_MULTIPLIER_ROUTE_ID
    assert review["lagrange_multiplier_action_form"] == LAGRANGE_MULTIPLIER_ACTION_FORM
    assert review["penalty_route_id"] == PENALTY_ROUTE_ID
    assert review["penalty_action_form"] == PENALTY_ACTION_FORM
    assert (
        review["first_A_relevant_ck_admissibility_rule_candidate_classification"]
        == FIRST_A_BRIDGE_RULE_CLASSIFICATION
    )


def test_a_bridge_ck_functional_embedding_review_accepts_required_points() -> None:
    review = _json(DEFAULT_OUT)
    assert review["review_criteria_count"] == 11
    assert review["review_criteria_accepted_count"] == 11
    assert {row["row_id"] for row in review["review_criteria"]} == {
        "admissibility_only_route_selected",
        "c_bridge_a_zero_preserved_as_rule",
        "bridge_tuple_context_preserved",
        "source_and_vacuum_u1_context_preserved",
        "multiplier_action_route_blocked",
        "penalty_route_unlicensed",
        "no_bridge_proof_or_route_alignment",
        "no_ck_action_embedding_or_variation",
        "no_current_sourced_maxwell_or_exchange",
        "no_closure_coupling_validation_or_promotion",
        "admissibility_rule_closeout_next_target_selected",
    }
    for key in [
        "functional_embedding_result_review_prepared",
        "functional_embedding_result_review_accepted",
        "review_accepts_admissibility_only_route",
        "packet_result_review_accepts_admissibility_only_route",
        "admissibility_rule_closeout_authorized",
        "admissibility_only_route_selected",
        "constraint_as_admissibility_rule_selected",
        "route_consistency_tuple_carried_forward",
        "lagrange_multiplier_route_blocked",
        "penalty_route_recorded",
        "penalty_route_unlicensed",
    ]:
        assert review[key] is True, key
    assert review["admissibility_rule_closeout_prepared"] is False


def test_a_bridge_ck_functional_embedding_review_blocks_shortcuts() -> None:
    review = _json(DEFAULT_OUT)
    for key in [
        "bridge_proof_claimed",
        "bridge_admissibility_proved",
        "route_consistency_tuple_proved",
        "field_equation_match_proved",
        "stress_energy_match_proved",
        "source_residual_match_proved",
        "dynamical_action_embedding_selected",
        "constraint_as_action_term_selected",
        "component_pairing_rule_selected",
        "multiplier_domain_selected",
        "covariance_control_established",
        "boundary_term_policy_selected",
        "variation_policy_selected",
        "gauge_dynamics_preservation_proved",
        "heterogeneous_tuple_norm_defined",
        "penalty_route_licensed",
        "quadratic_penalty_route_licensed",
        "ck_action_embedding_constructed",
        "C_k_action_embedding_constructed",
        "ck_variation_executed",
        "C_k_variation_executed",
        "lambda_variation_executed",
        "metric_variation_of_candidate_executed",
        "A_variation_of_candidate_executed",
        "J_nu_derived",
        "psi_current_route_constructed",
        "external_current_native_derivation_selected",
        "sourced_maxwell_equation_derived",
        "sourced_maxwell_route_derived",
        "matter_current_exchange_route_proved",
        "matter_gauge_energy_exchange_proved",
        "full_em_closure_claimed",
        "qft_gr_closure_claimed",
        "semiclassical_coupling_authorized",
        "empirical_validation_claimed",
        "master_action_promoted",
        "canonical_master_action_promoted",
        "phase2_readiness_claim",
        "seam_closure_claim",
    ]:
        assert review[key] is False, key
    for phrase in [
        "accepts the admissibility-only route as a rule only",
        "not as an action term",
        "preserves C_bridge^A = 0",
        "keeps the multiplier/action route blocked",
        "keeps the penalty route unlicensed",
        "does not functionalize C_bridge^A",
        "does not embed it in S_C",
        "does not define a C_k action term",
        "does not execute C_k variation",
        "does not prove bridge admissibility",
        "does not derive J^nu",
        "does not derive sourced Maxwell",
        "does not close EM",
        "does not close QFT-GR",
        "does not promote the master action",
    ]:
        assert phrase in review["non_claim_boundary"], phrase


def test_a_bridge_ck_functional_embedding_review_validation_policy_not_run() -> None:
    review = _json(DEFAULT_OUT)
    policy = review["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False
    assert policy["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"


def test_a_bridge_ck_functional_embedding_review_rotates_to_closeout() -> None:
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
        "ToeNativeABridgeAdmissibilityCKFunctionalEmbeddingPacketResultReview.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_"
        "RESULT_REVIEW_20260622_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["packet_result"] == "REVIEW_ACCEPTED"
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["admissibility_rule_closeout_authorized"] == "yes"
    assert consumed["admissibility_rule_closeout_prepared"] == "no"
    assert consumed["admissibility_only_route_selected"] == "yes"
    assert consumed["lagrange_multiplier_route_blocked"] == "yes"
    assert consumed["penalty_route_unlicensed"] == "yes"
    assert consumed["penalty_route_licensed"] == "no"
    assert consumed["ck_variation_executed"] == "no"
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
    assert active_row["outcome_id"] == OUTCOME_ID
    assert active_row["packet_result"] == "REVIEW_ACCEPTED"
    assert active_row["review_result"] == OUTCOME_ID
    assert active_row["admissibility_rule_closeout_authorized"] == "yes"
    assert active_row["admissibility_rule_closeout_prepared"] == "no"
    assert active_row["admissibility_only_route_selected"] == "yes"
    assert active_row["constraint_as_action_term_selected"] == "no"
    assert active_row["lagrange_multiplier_route_blocked"] == "yes"
    assert active_row["penalty_route_unlicensed"] == "yes"
    assert active_row["penalty_route_licensed"] == "no"
    assert active_row["ck_action_embedding_constructed"] == "no"
    assert active_row["C_k_action_embedding_constructed"] == "no"
    assert active_row["ck_variation_executed"] == "no"
    assert active_row["C_k_variation_executed"] == "no"
    assert active_row["J_nu_derived"] == "no"
    assert active_row["sourced_maxwell_equation_derived"] == "no"
    assert active_row["matter_current_exchange_route_proved"] == "no"
    assert active_row["full_em_closure_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_a_bridge_ck_functional_embedding_review_mirrors() -> None:
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
        "ToeNativeABridgeAdmissibilityCKFunctionalEmbeddingPacketResultReview",
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_toe_native_A_bridge_admissibility_ck_admissibility_rule_closeout",
        "HISTORICAL_TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_"
        "PACKET_RESULT_REVIEW_CURRENT_LIVE_NEXT_TARGET_v0: "
        "review_toe_native_A_bridge_admissibility_ck_functional_embedding_packet_result",
        A_BRIDGE_CANDIDATE_ID,
        A_BRIDGE_CONSTRAINT_FORM,
        A_BRIDGE_CONSTRAINT_EQUATION,
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        ADMISSIBILITY_ONLY_ROUTE_ID,
        LAGRANGE_MULTIPLIER_ROUTE_ID,
        PENALTY_ROUTE_ID,
        LAGRANGE_MULTIPLIER_ACTION_FORM,
        PENALTY_ACTION_FORM,
        "accepts the admissibility-only route as a rule only",
        "preserves C_bridge^A = 0",
        "keeps the multiplier/action route blocked",
        "keeps the penalty route unlicensed",
        "does not functionalize C_bridge^A",
        "does not embed it in S_C",
        "does not execute C_k variation",
        "does not prove bridge admissibility",
        "does not derive J^nu",
        "does not derive sourced Maxwell",
        "does not close EM",
        "does not close QFT-GR",
        "master-action promotion remains blocked",
        "NOT_RUN",
    ]:
        assert token in joined


def test_a_bridge_ck_functional_embedding_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_a_bridge_admissibility_ck_functional_embedding_packet_result_review_gate.py"
    )
