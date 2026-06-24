from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.toe_native_a_transport_consistency_ck_admissibility_rule_closeout_report import (
    ARTIFACT_ID,
    BRIDGE_RULE_CLOSEOUT_OUTCOME,
    CLOSEOUT_RESULT,
    CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME,
    FUNCTIONAL_EMBEDDING_REVIEW_PATH,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    SOURCE_RULE_CLOSEOUT_OUTCOME,
    TRANSPORT_CLOSEOUT_RULE_CLASSIFICATION,
    TRANSPORT_CLOSEOUT_RULE_ROLE,
    build_toe_native_a_transport_consistency_ck_admissibility_rule_closeout,
)
from formal.python.tools.toe_native_a_transport_consistency_ck_functional_embedding_packet_result_review_report import (
    ADMISSIBILITY_ONLY_ROUTE_ID,
    A_BRIDGE_CONSTRAINT_EQUATION,
    A_BRIDGE_CONSTRAINT_FORM,
    DIRECT_DYNAMICAL_LAW_INTERPRETATION_ID,
    LAGRANGE_MULTIPLIER_ACTION_FORM,
    PENALTY_ACTION_FORM,
    TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
    TRANSPORT_CANDIDATE_ID,
    TRANSPORT_CONSTRAINT_EQUATION,
    TRANSPORT_CONSTRAINT_FORM,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "toe_native_a_transport_consistency_ck_admissibility_rule_closeout_report.py"
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


def test_a_transport_ck_closeout_files_exist() -> None:
    for path in [
        FUNCTIONAL_EMBEDDING_REVIEW_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_a_transport_ck_closeout_accepts_review_and_selects_synthesis() -> None:
    review = _json(FUNCTIONAL_EMBEDDING_REVIEW_PATH)
    closeout = _json(DEFAULT_OUT)
    assert review["outcome_id"] == FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME
    assert closeout["artifact_id"] == ARTIFACT_ID
    assert closeout["schema_id"] == SCHEMA_ID
    assert closeout["packet_id"] == PACKET_ID
    assert closeout["prepared"] is True
    assert closeout["accepted"] is True
    assert closeout["outcome_id"] == OUTCOME_ID
    assert closeout["closeout_result"] == CLOSEOUT_RESULT
    assert closeout["packet_result"] == "CLOSEOUT_ACCEPTED"
    assert closeout["packet_classification"] == PACKET_CLASSIFICATION
    assert closeout["consumed_target"] == CONSUMED_TARGET
    assert closeout["selected_next_target"] == NEXT_TARGET
    assert closeout["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert closeout["functional_embedding_review_outcome"] == (
        FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME
    )
    assert build_toe_native_a_transport_consistency_ck_admissibility_rule_closeout() == (
        closeout
    )


def test_a_transport_ck_closeout_preserves_rule_forms_and_context() -> None:
    closeout = _json(DEFAULT_OUT)
    assert closeout["transport_candidate_id"] == TRANSPORT_CANDIDATE_ID
    assert closeout["transport_constraint_form"] == TRANSPORT_CONSTRAINT_FORM
    assert closeout["transport_constraint_equation"] == TRANSPORT_CONSTRAINT_EQUATION
    assert (
        closeout["transport_admissibility_constraint_form"]
        == TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert closeout["transport_component_count"] == 5
    assert closeout["source_rule_closeout_outcome"] == SOURCE_RULE_CLOSEOUT_OUTCOME
    assert closeout["bridge_closeout_outcome"] == BRIDGE_RULE_CLOSEOUT_OUTCOME
    assert closeout["A_bridge_constraint_form"] == A_BRIDGE_CONSTRAINT_FORM
    assert closeout["A_bridge_constraint_equation"] == A_BRIDGE_CONSTRAINT_EQUATION
    assert closeout["selected_embedding_route_id"] == ADMISSIBILITY_ONLY_ROUTE_ID
    assert closeout["lagrange_multiplier_action_form"] == LAGRANGE_MULTIPLIER_ACTION_FORM
    assert closeout["penalty_action_form"] == PENALTY_ACTION_FORM
    assert (
        closeout["direct_dynamical_law_interpretation_id"]
        == DIRECT_DYNAMICAL_LAW_INTERPRETATION_ID
    )
    assert (
        closeout["transport_closeout_rule_classification"]
        == TRANSPORT_CLOSEOUT_RULE_CLASSIFICATION
    )
    assert closeout["transport_rule_role"] == TRANSPORT_CLOSEOUT_RULE_ROLE


def test_a_transport_ck_closeout_accepts_required_points() -> None:
    closeout = _json(DEFAULT_OUT)
    assert closeout["closeout_criteria_count"] == 13
    assert closeout["closeout_criteria_accepted_count"] == 13
    assert {row["row_id"] for row in closeout["closeout_criteria"]} == {
        "consumes_expected_closeout_target",
        "c_transport_a_zero_closed_as_rule",
        "transport_tuple_preserved",
        "source_and_bridge_context_preserved",
        "vacuum_u1_scope_preserved",
        "not_action_term_or_dynamical_law",
        "multiplier_and_penalty_routes_blocked",
        "no_transport_proof_or_concrete_functional",
        "no_ck_action_embedding_or_variation",
        "no_current_sourced_maxwell_or_exchange",
        "no_closure_coupling_phase_validation_or_promotion",
        "full_toeformal_aggregate_recorded_not_run",
        "synthesis_packet_authorized",
    }
    for key in [
        "admissibility_rule_closeout_prepared",
        "admissibility_rule_closeout_accepted",
        "third_A_relevant_ck_admissibility_rule_candidate_closed",
        "A_transport_consistency_rule_candidate_closed",
        "vacuum_U1_transport_consistency_rule_closed",
        "derivation_chain_stability_rule_closed",
        "transport_admissibility_rule_closed_as_vacuum_U1_derivation_chain_stability_rule",
        "candidate_recorded_as_rule_only",
        "admissibility_only_route_selected",
        "constraint_as_admissibility_rule_selected",
        "transport_tuple_carried_forward",
        "source_and_bridge_context_preserved",
        "vacuum_u1_scope_preserved",
        "lagrange_multiplier_route_blocked",
        "penalty_route_unlicensed",
        "direct_dynamical_law_interpretation_blocked",
        "three_rule_family_synthesis_packet_authorized",
        "A_ck_source_bridge_transport_triad_ready_for_synthesis",
        "source_admissibility_rule_closed",
        "bridge_admissibility_rule_closed",
        "transport_consistency_rule_closed",
    ]:
        assert closeout[key] is True, key
    assert closeout["three_rule_family_synthesis_packet_prepared"] is False


def test_a_transport_ck_closeout_blocks_shortcuts() -> None:
    closeout = _json(DEFAULT_OUT)
    for key in [
        "candidate_recorded_as_action_term",
        "candidate_recorded_as_new_physical_law",
        "candidate_recorded_as_new_dynamical_law",
        "dynamical_action_embedding_selected",
        "constraint_as_action_term_selected",
        "transport_candidate_functional_defined",
        "component_pairing_rule_selected",
        "transport_map_domains_codomains_selected",
        "heterogeneous_tuple_norm_defined",
        "penalty_route_licensed",
        "direct_dynamical_law_interpretation_selected",
        "fully_concrete_ck_functional_defined",
        "C_k_action_embedding_constructed",
        "candidate_action_insertion_executed",
        "C_k_variation_executed",
        "lambda_variation_executed",
        "metric_variation_of_candidate_executed",
        "A_variation_of_candidate_executed",
        "transport_consistency_claimed",
        "transport_consistency_proved",
        "transport_proof_claimed",
        "transport_components_proved",
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
        "canonical_master_action_promoted",
        "seam_closure_claim",
        "A_ck_source_bridge_transport_rule_family_synthesized",
    ]:
        assert closeout[key] is False, key
    for phrase in [
        "closes C_transport^A = 0 only as an admissibility-only",
        "route-stability rule",
        "not an action term",
        "not a dynamical law",
        "does not prove transport consistency",
        "does not prove any transport component",
        "does not define a concrete C_transport^A functional",
        "does not embed C_transport^A into the action",
        "does not execute C_k variation",
        "does not derive J^nu",
        "does not derive sourced Maxwell",
        "does not prove matter/current exchange",
        "does not close EM",
        "does not close QFT-GR",
        "does not authorize Phase 2",
        "does not promote the master action",
        "NOT_RUN",
    ]:
        assert phrase in closeout["non_claim_boundary"], phrase


def test_a_transport_ck_closeout_validation_policy_not_run() -> None:
    closeout = _json(DEFAULT_OUT)
    policy = closeout["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == "NOT_RUN"
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False
    assert policy["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"


def test_a_transport_ck_closeout_rotates_to_synthesis_packet() -> None:
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
        "ToeNativeATransportConsistencyCKAdmissibilityRuleCloseout.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_ADMISSIBILITY_RULE_CLOSEOUT_"
        "20260623_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["packet_result"] == "CLOSEOUT_ACCEPTED"
    assert consumed["closeout_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["three_rule_family_synthesis_packet_authorized"] == "yes"
    assert consumed["three_rule_family_synthesis_packet_prepared"] == "no"
    assert consumed["transport_consistency_rule_closed"] == "yes"
    assert consumed["A_ck_source_bridge_transport_rule_family_synthesized"] == "no"
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
    assert active_row["packet_result"] == "CLOSEOUT_ACCEPTED"
    assert active_row["closeout_result"] == OUTCOME_ID
    assert active_row["selected_next_target"] == NEXT_TARGET
    assert active_row["three_rule_family_synthesis_packet_authorized"] == "yes"
    assert active_row["three_rule_family_synthesis_packet_prepared"] == "no"
    assert active_row["transport_constraint_equation"] == TRANSPORT_CONSTRAINT_EQUATION
    assert active_row["transport_consistency_rule_closed"] == "yes"
    assert active_row["A_ck_source_bridge_transport_triad_ready_for_synthesis"] == "yes"
    assert active_row["A_ck_source_bridge_transport_rule_family_synthesized"] == "no"
    assert active_row["constraint_as_action_term_selected"] == "no"
    assert active_row["transport_candidate_functional_defined"] == "no"
    assert active_row["C_k_action_embedding_constructed"] == "no"
    assert active_row["C_k_variation_executed"] == "no"
    assert active_row["J_nu_derived"] == "no"
    assert active_row["sourced_maxwell_equation_derived"] == "no"
    assert active_row["matter_current_exchange_route_proved"] == "no"
    assert active_row["full_em_closure_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["phase2_readiness_claim"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_a_transport_ck_closeout_mirrors() -> None:
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
        CLOSEOUT_RESULT,
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        "ToeNativeATransportConsistencyCKAdmissibilityRuleCloseout",
        (
            "CURRENT_LIVE_NEXT_TARGET_v0: "
            "prepare_toe_native_A_ck_source_bridge_transport_rule_family_synthesis_packet"
        ),
        "HISTORICAL_TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_ADMISSIBILITY_RULE_"
        "CLOSEOUT_CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_toe_native_A_transport_consistency_ck_admissibility_rule_closeout",
        TRANSPORT_CANDIDATE_ID,
        TRANSPORT_CONSTRAINT_FORM,
        TRANSPORT_CONSTRAINT_EQUATION,
        ADMISSIBILITY_ONLY_ROUTE_ID,
        LAGRANGE_MULTIPLIER_ACTION_FORM,
        PENALTY_ACTION_FORM,
        DIRECT_DYNAMICAL_LAW_INTERPRETATION_ID,
        "closes C_transport^A = 0 only as an admissibility-only",
        "route-stability rule",
        "not an action term",
        "not a dynamical law",
        "does not prove transport consistency",
        "does not derive J^nu",
        "does not derive sourced Maxwell",
        "does not close EM",
        "does not close QFT-GR",
        "master-action promotion remains blocked",
        "NOT_RUN",
    ]:
        assert token in joined


def test_a_transport_ck_closeout_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_toe_native_a_transport_consistency_ck_admissibility_rule_closeout_gate.py"
    )
