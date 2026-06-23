from __future__ import annotations

import json
import sys
from pathlib import Path

sys.setrecursionlimit(10000)

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.toe_native_a_source_admissibility_ck_constraint_candidate_packet_result_review_report import (
    DEFAULT_OUT as CANDIDATE_REVIEW_PATH,
    OUTCOME_ID as CANDIDATE_REVIEW_OUTCOME,
)
from formal.python.tools.toe_native_a_source_admissibility_ck_functional_embedding_packet_report import (
    ADMISSIBILITY_CONSTRAINT_FORM,
    ADMISSIBILITY_ONLY_ROUTE_ID,
    ARTIFACT_ID,
    CANDIDATE_CONSTRAINT_EQUATION,
    CANDIDATE_CONSTRAINT_FORM,
    CANDIDATE_CONSTRAINT_ID,
    COMPONENT_PAIRING_FORM,
    CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    DIRECT_DIVERGENCE_INSERTION_FORM,
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
    QFTGR_AGGREGATE_PATH,
    QUADRATIC_PENALTY_ACTION_FORM,
    QUADRATIC_PENALTY_ROUTE_ID,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    SELECTED_A_CK_CONSTRAINT_FAMILY,
    WEAK_INTEGRATED_FORM,
    build_toe_native_a_source_admissibility_ck_functional_embedding_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_a_source_admissibility_ck_functional_embedding_packet_report.py"
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


def test_a_source_admissibility_ck_functional_embedding_files_exist() -> None:
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


def test_a_source_admissibility_ck_functional_embedding_records_routes() -> None:
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
    assert packet["selected_A_ck_constraint_family"] == SELECTED_A_CK_CONSTRAINT_FAMILY
    assert packet["candidate_constraint_id"] == CANDIDATE_CONSTRAINT_ID
    assert packet["candidate_constraint_form"] == CANDIDATE_CONSTRAINT_FORM
    assert packet["candidate_constraint_equation"] == CANDIDATE_CONSTRAINT_EQUATION
    assert packet["admissibility_constraint_form"] == ADMISSIBILITY_CONSTRAINT_FORM
    assert packet["lagrange_multiplier_action_form"] == LAGRANGE_MULTIPLIER_ACTION_FORM
    assert packet["direct_divergence_insertion_form"] == DIRECT_DIVERGENCE_INSERTION_FORM
    assert packet["component_pairing_form"] == COMPONENT_PAIRING_FORM
    assert packet["weak_integrated_form"] == WEAK_INTEGRATED_FORM
    assert packet["quadratic_penalty_action_form"] == QUADRATIC_PENALTY_ACTION_FORM
    assert (
        build_toe_native_a_source_admissibility_ck_functional_embedding_packet()
        == packet
    )


def test_a_source_admissibility_ck_functional_embedding_route_statuses() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["embedding_route_count"] == 3
    routes = {row["route_id"]: row for row in packet["embedding_routes"]}
    assert routes[ADMISSIBILITY_ONLY_ROUTE_ID]["status"] == (
        "selected_non_dynamical_admissibility_rule"
    )
    assert routes[ADMISSIBILITY_ONLY_ROUTE_ID]["selected_for_current_packet"] is True
    assert routes[ADMISSIBILITY_ONLY_ROUTE_ID]["action_term_selected"] is False
    assert routes[LAGRANGE_MULTIPLIER_ROUTE_ID]["status"] == (
        "blocked_by_multiplier_domain_pairing_boundary_variation_and_dynamics_scope"
    )
    assert routes[LAGRANGE_MULTIPLIER_ROUTE_ID]["selected_for_current_packet"] is False
    for reason in [
        "lambda_nu domain not selected",
        "component pairing rule not selected",
        "boundary terms not controlled",
        "variation policy not selected",
        "higher-derivative analysis not completed",
        "no proof that the action term preserves intended gauge dynamics",
    ]:
        assert reason in routes[LAGRANGE_MULTIPLIER_ROUTE_ID]["blocking_reasons"]
    assert routes[QUADRATIC_PENALTY_ROUTE_ID]["status"] == (
        "recorded_unlicensed_dynamical_penalty"
    )
    assert routes[QUADRATIC_PENALTY_ROUTE_ID]["selected_for_current_packet"] is False
    assert packet["selected_embedding_route_id"] == ADMISSIBILITY_ONLY_ROUTE_ID
    assert packet["review_row_count"] == 10
    assert packet["review_row_accepted_count"] == 10
    assert {row["row_id"] for row in packet["review_rows"]} == {
        "consumes_expected_functional_embedding_target",
        "vacuum_conservation_residual_candidate_carried_forward",
        "vacuum_u1_route_context_carried_forward",
        "three_embedding_routes_recorded",
        "admissibility_only_route_selected",
        "lagrange_multiplier_route_blocked",
        "quadratic_penalty_route_unlicensed",
        "no_action_embedding_or_variation_executed",
        "no_current_or_sourced_em_route",
        "no_closure_coupling_validation_or_promotion",
    }


def test_a_source_admissibility_ck_functional_embedding_blocks_action_claims() -> None:
    packet = _json(DEFAULT_OUT)
    for key in [
        "functional_embedding_packet_prepared",
        "functional_embedding_options_recorded",
        "admissibility_only_route_selected",
        "constraint_as_admissibility_rule_selected",
        "lagrange_multiplier_route_recorded",
        "lagrange_multiplier_route_blocked",
        "quadratic_penalty_route_recorded",
        "A_relevant_C_k_rule_candidate_review_accepted",
    ]:
        assert packet[key] is True, key
    for key in [
        "dynamical_action_embedding_selected",
        "constraint_as_action_term_selected",
        "weak_integrated_form_boundary_controlled",
        "quadratic_penalty_route_licensed",
        "constraint_multiplier_type_selected",
        "constraint_term_selected",
        "lambda_nu_domain_selected",
        "component_pairing_rule_selected",
        "variation_policy_selected",
        "higher_derivative_analysis_completed",
        "higher_derivative_scope_resolved",
        "boundary_terms_controlled",
        "gauge_dynamics_preservation_proved",
        "fully_concrete_ck_functional_selected",
        "fully_concrete_ck_functional_defined",
        "ck_action_embedding_constructed",
        "C_k_action_embedding_constructed",
        "ck_variation_executed",
        "C_k_variation_executed",
        "lambda_variation_executed",
        "metric_variation_of_candidate_executed",
        "A_variation_of_candidate_executed",
        "quadratic_penalty_variation_executed",
        "J_nu_derived",
        "psi_current_route_constructed",
        "external_current_native_derivation_selected",
        "sourced_maxwell_equation_derived",
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
        assert packet[key] is False, key
    for phrase in [
        "selects the admissibility-only route",
        "does not functionalize the candidate",
        "does not embed it in S_C",
        "does not select lambda_nu or its domain",
        "does not select a component pairing rule",
        "does not control boundary terms",
        "does not select a variation policy",
        "does not complete higher-derivative analysis",
        "does not prove preservation of the intended gauge dynamics",
        "does not license the quadratic penalty route",
        "does not execute C_k variation",
        "does not derive J^nu",
        "does not derive sourced Maxwell",
        "does not close EM",
        "does not close QFT-GR",
    ]:
        assert phrase in packet["non_claim_boundary"], phrase


def test_a_source_admissibility_ck_functional_embedding_validation_policy_not_run() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False
    assert policy["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"


def test_a_source_admissibility_ck_functional_embedding_rotates_to_review_target() -> None:
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
        "ToeNativeASourceAdmissibilityCKFunctionalEmbeddingPacket.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_"
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
    assert consumed["quadratic_penalty_route_licensed"] == "no"
    assert consumed["ck_variation_executed"] == "no"
    assert consumed["J_nu_derived"] == "no"
    assert consumed["sourced_maxwell_equation_derived"] == "no"

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
    assert active_row["lambda_nu_domain_selected"] == "no"
    assert active_row["component_pairing_rule_selected"] == "no"
    assert active_row["variation_policy_selected"] == "no"
    assert active_row["higher_derivative_analysis_completed"] == "no"
    assert active_row["boundary_terms_controlled"] == "no"
    assert active_row["gauge_dynamics_preservation_proved"] == "no"
    assert active_row["ck_variation_executed"] == "no"
    assert active_row["J_nu_derived"] == "no"
    assert active_row["sourced_maxwell_equation_derived"] == "no"
    assert active_row["matter_current_exchange_route_proved"] == "no"
    assert active_row["full_em_closure_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_a_source_admissibility_ck_functional_embedding_mirrors() -> None:
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
        "ToeNativeASourceAdmissibilityCKFunctionalEmbeddingPacket",
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "review_toe_native_A_source_admissibility_ck_functional_embedding_packet_result",
        ADMISSIBILITY_ONLY_ROUTE_ID,
        LAGRANGE_MULTIPLIER_ROUTE_ID,
        QUADRATIC_PENALTY_ROUTE_ID,
        ADMISSIBILITY_CONSTRAINT_FORM,
        LAGRANGE_MULTIPLIER_ACTION_FORM,
        COMPONENT_PAIRING_FORM,
        WEAK_INTEGRATED_FORM,
        QUADRATIC_PENALTY_ACTION_FORM,
        "selects only the vacuum U(1) admissibility-only route",
        "does not functionalize the candidate",
        "does not embed it in S_C",
        "does not select lambda_nu or its domain",
        "does not select a component pairing rule",
        "does not complete higher-derivative analysis",
        "does not derive J^nu",
        "does not derive sourced Maxwell",
        "does not close EM",
        "does not close QFT-GR",
        "master-action promotion remains blocked",
        "NOT_RUN",
    ]:
        assert token in joined


def test_a_source_admissibility_ck_functional_embedding_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_a_source_admissibility_ck_functional_embedding_packet_gate.py"
    )
