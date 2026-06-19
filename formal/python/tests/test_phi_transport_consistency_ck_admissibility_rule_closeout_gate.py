from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.phi_transport_consistency_ck_admissibility_rule_closeout_report import (
    ADMISSIBILITY_ONLY_ROUTE_ID,
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    BRIDGE_RULE_CLOSEOUT_OUTCOME,
    CLOSEOUT_RESULT,
    CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    DIRECT_DYNAMICAL_LAW_INTERPRETATION_ID,
    DIRECT_DYNAMICAL_LAW_INTERPRETATION_STATUS,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME,
    FUNCTIONAL_EMBEDDING_REVIEW_PATH,
    FUNCTIONAL_EMBEDDING_REVIEW_RESULT,
    LAGRANGE_MULTIPLIER_ACTION_FORM,
    LAGRANGE_MULTIPLIER_ROUTE_STATUS,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PENALTY_ACTION_FORM,
    PENALTY_ROUTE_STATUS,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    RULE_FAMILY_SYNTHESIS_OUTCOME_HINT,
    SCHEMA_ID,
    SELECTED_CK_CONSTRAINT_FAMILY,
    SELECTED_CK_OPTION_CLASS,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    SOURCE_RULE_CLOSEOUT_OUTCOME,
    THIRD_RULE_CLASSIFICATION,
    TRANSPORT_ACTION_EMBEDDING_CHAIN_FORM,
    TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
    TRANSPORT_CANDIDATE_ID,
    TRANSPORT_CANDIDATE_TYPE,
    TRANSPORT_CLOSEOUT_RULE_CLASSIFICATION,
    TRANSPORT_COMPONENTS,
    TRANSPORT_CONSTRAINT_EQUATION,
    TRANSPORT_CONSTRAINT_FORM,
    TRANSPORT_RULE_CLASSIFICATION,
    TRANSPORT_RULE_EPISTEMIC_STATUS,
    TRANSPORT_CLOSEOUT_RULE_ROLE,
    build_phi_transport_consistency_ck_admissibility_rule_closeout,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "phi_transport_consistency_ck_admissibility_rule_closeout_report.py"
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


def test_phi_transport_consistency_ck_admissibility_rule_closeout_files_exist() -> None:
    for path in [
        FUNCTIONAL_EMBEDDING_REVIEW_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_phi_transport_consistency_ck_admissibility_rule_closeout_accepts_review() -> None:
    review = _json(FUNCTIONAL_EMBEDDING_REVIEW_PATH)
    closeout = _json(DEFAULT_OUT)
    assert review["outcome_id"] == FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME
    assert review["review_result"] == FUNCTIONAL_EMBEDDING_REVIEW_RESULT
    assert closeout["schema_id"] == SCHEMA_ID
    assert closeout["packet_id"] == PACKET_ID
    assert closeout["prepared"] is True
    assert closeout["accepted"] is True
    assert closeout["outcome_id"] == OUTCOME_ID
    assert closeout["closeout_result"] == CLOSEOUT_RESULT
    assert closeout["packet_classification"] == PACKET_CLASSIFICATION
    assert closeout["consumed_target"] == CONSUMED_TARGET
    assert closeout["selected_next_target"] == NEXT_TARGET
    assert closeout["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert build_phi_transport_consistency_ck_admissibility_rule_closeout() == closeout


def test_phi_transport_consistency_ck_admissibility_rule_closeout_preserves_forms() -> None:
    closeout = _json(DEFAULT_OUT)
    assert closeout["selected_ck_option_class"] == SELECTED_CK_OPTION_CLASS
    assert closeout["selected_ck_constraint_family"] == SELECTED_CK_CONSTRAINT_FAMILY
    assert (
        closeout["third_phi_relevant_ck_admissibility_rule_candidate_classification"]
        == THIRD_RULE_CLASSIFICATION
    )
    assert closeout["transport_rule_classification"] == TRANSPORT_RULE_CLASSIFICATION
    assert closeout["transport_closeout_rule_classification"] == (
        TRANSPORT_CLOSEOUT_RULE_CLASSIFICATION
    )
    assert closeout["transport_rule_role"] == TRANSPORT_CLOSEOUT_RULE_ROLE
    assert closeout["transport_rule_epistemic_status"] == TRANSPORT_RULE_EPISTEMIC_STATUS
    assert closeout["transport_candidate_id"] == TRANSPORT_CANDIDATE_ID
    assert closeout["transport_candidate_type"] == TRANSPORT_CANDIDATE_TYPE
    assert closeout["transport_constraint_form"] == TRANSPORT_CONSTRAINT_FORM
    assert closeout["transport_constraint_equation"] == TRANSPORT_CONSTRAINT_EQUATION
    assert closeout["transport_admissibility_constraint_form"] == (
        TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert closeout["transport_component_forms"] == [
        row["component_form"] for row in TRANSPORT_COMPONENTS
    ]
    assert closeout["transport_action_embedding_chain_form"] == (
        TRANSPORT_ACTION_EMBEDDING_CHAIN_FORM
    )
    assert closeout["source_rule_closeout_outcome"] == SOURCE_RULE_CLOSEOUT_OUTCOME
    assert closeout["source_candidate_constraint_id"] == SOURCE_CANDIDATE_CONSTRAINT_ID
    assert closeout["source_candidate_constraint_form"] == SOURCE_CANDIDATE_CONSTRAINT_FORM
    assert closeout["source_candidate_constraint_equation"] == (
        SOURCE_CANDIDATE_CONSTRAINT_EQUATION
    )
    assert closeout["source_admissibility_constraint_form"] == (
        SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert closeout["bridge_rule_closeout_outcome"] == BRIDGE_RULE_CLOSEOUT_OUTCOME
    assert closeout["bridge_constraint_form"] == BRIDGE_CONSTRAINT_FORM
    assert closeout["bridge_constraint_equation"] == BRIDGE_CONSTRAINT_EQUATION
    assert closeout["bridge_admissibility_constraint_form"] == (
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert closeout["selected_embedding_route_id"] == ADMISSIBILITY_ONLY_ROUTE_ID
    assert closeout["lagrange_multiplier_route_status"] == LAGRANGE_MULTIPLIER_ROUTE_STATUS
    assert closeout["lagrange_multiplier_action_form"] == LAGRANGE_MULTIPLIER_ACTION_FORM
    assert closeout["penalty_route_status"] == PENALTY_ROUTE_STATUS
    assert closeout["penalty_action_form"] == PENALTY_ACTION_FORM
    assert closeout["direct_dynamical_law_interpretation_id"] == (
        DIRECT_DYNAMICAL_LAW_INTERPRETATION_ID
    )
    assert closeout["direct_dynamical_law_interpretation_status"] == (
        DIRECT_DYNAMICAL_LAW_INTERPRETATION_STATUS
    )


def test_phi_transport_consistency_ck_admissibility_rule_closeout_records_points() -> None:
    closeout = _json(DEFAULT_OUT)
    assert closeout["closeout_criteria_count"] == 13
    assert closeout["closeout_criteria_accepted_count"] == 13
    assert {row["row_id"] for row in closeout["closeout_criteria"]} == {
        "functional_embedding_review_accepts_admissibility_only",
        "third_phi_relevant_ck_rule_candidate_closed",
        "transport_tuple_preserved",
        "transport_condition_preserved",
        "transport_components_preserved_unproved",
        "source_and_bridge_context_preserved",
        "closed_as_transport_consistency_rule_candidate",
        "not_action_term_or_dynamical_law",
        "multiplier_penalty_and_direct_law_routes_remain_blocked",
        "no_variation_generation_or_potential_derivation",
        "no_transport_proof_qft_gr_closure_or_master_promotion",
        "full_toeformal_aggregate_recorded_not_run",
        "three_rule_family_synthesis_packet_authorized",
    }
    for key in [
        "admissibility_rule_closeout_prepared",
        "admissibility_rule_closeout_accepted",
        "third_phi_relevant_ck_admissibility_rule_candidate_closed",
        "transport_consistency_rule_candidate_closed",
        "derivation_chain_stability_rule_closed",
        "transport_admissibility_rule_closed_as_derivation_chain_stability_rule",
        "admissibility_only_route_selected",
        "admissibility_only_interpretation_retained",
        "constraint_as_admissibility_rule_selected",
        "candidate_recorded_as_rule_only",
        "transport_tuple_carried_forward",
        "transport_constraint_carried_forward",
        "transport_components_carried_forward",
        "transport_components_preserved_unproved",
        "source_and_bridge_context_preserved",
        "known_phi_chain_preserved",
        "lagrange_multiplier_route_recorded",
        "lagrange_multiplier_route_blocked",
        "penalty_route_recorded",
        "direct_dynamical_law_interpretation_recorded",
        "direct_dynamical_law_interpretation_blocked",
        "three_rule_family_synthesis_packet_authorized",
        "source_admissibility_rule_synthesis_entry_preserved",
        "bridge_admissibility_rule_synthesis_entry_preserved",
        "transport_consistency_rule_synthesis_entry_preserved",
        "penalty_would_change_dynamics",
    ]:
        assert closeout[key] is True, key
    assert closeout["phi_ck_admissibility_rule_family_contains_count"] == 3
    assert closeout["three_rule_family_synthesis_packet_prepared"] is False
    assert closeout["three_rule_family_synthesis_outcome_hint"] == (
        RULE_FAMILY_SYNTHESIS_OUTCOME_HINT
    )


def test_phi_transport_consistency_ck_admissibility_rule_closeout_blocks_shortcuts() -> None:
    closeout = _json(DEFAULT_OUT)
    for key in [
        "constraint_as_action_term_selected",
        "dynamical_action_embedding_selected",
        "candidate_recorded_as_new_physical_law",
        "candidate_recorded_as_action_term",
        "transport_candidate_recorded_as_action_term",
        "transport_candidate_recorded_as_new_dynamical_law",
        "penalty_route_licensed",
        "direct_dynamical_law_interpretation_selected",
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
        "heterogeneous_tuple_norm_defined",
        "candidate_action_insertion_executed",
        "ck_variation_executed",
        "ck_variation_authorized",
        "lambda_variation_executed",
        "metric_variation_of_candidate_executed",
        "phi_variation_of_candidate_executed",
        "penalty_variation_executed",
        "ck_family_claimed_as_physical_law",
        "ck_action_embedding_claimed",
        "transport_candidate_rule_proved",
        "transport_consistency_claimed",
        "transport_consistency_proved",
        "transport_proof_claimed",
        "transport_components_proved",
        "full_route_alignment_proof_claimed",
        "full_route_alignment_proved",
        "route_chain_compatibility_proved",
        "source_admissibility_proved",
        "bridge_admissibility_proved",
        "native_phi_derivation_claimed",
        "phi_generated_by_ck_claimed",
        "phi_generation_theorem_claimed",
        "native_generation_theorem_claimed",
        "derived_v_phi_claimed",
        "v_phi_derivation_claimed",
        "potential_derived",
        "new_conservation_proof_claimed",
        "new_source_admissibility_proof_claimed",
        "source_admissibility_claimed",
        "qft_gr_closure_claimed",
        "qft_gr_solved",
        "qft_gr_seam_closed",
        "semiclassical_coupling_authorized",
        "semiclassical_coupling_claimed",
        "master_action_promoted",
        "master_action_promotion_authorized",
        "canonical_master_action_promoted",
        "toe_native_matter_derivation_claimed",
        "standard_model_derivation_claimed",
        "empirical_validation_claimed",
        "public_readiness_claimed",
        "phase2_readiness_claim",
        "pillar_completion_inferred",
        "seam_closure_claim",
        "another_phi_derivation_selected",
    ]:
        assert closeout[key] is False, key
    for phrase in [
        "third phi-relevant C_k admissibility rule candidate only",
        "C_transport^phi = 0",
        "transport-consistency derivation-chain stability admissibility-rule candidate",
        "not as an action term",
        "not as a transport proof",
        "not as a native phi generation theorem",
        "not as V(phi) derivation",
        "not as QFT-GR closure",
        "not as master-action promotion",
        "does not execute C_k variation",
        "does not prove full route alignment",
        "full ToeFormal aggregate is recorded as NOT_RUN",
        "not another immediate phi derivation",
    ]:
        assert phrase in closeout["non_claim_boundary"], phrase


def test_phi_transport_consistency_ck_admissibility_rule_closeout_validation_policy() -> None:
    closeout = _json(DEFAULT_OUT)
    policy = closeout["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == (
        FULL_TOEFORMAL_AGGREGATE_STATUS
    )
    assert policy["full_toeformal_aggregate_status_for_packet"] == (
        FULL_TOEFORMAL_AGGREGATE_STATUS
    )
    assert policy["full_toeformal_aggregate_passed"] is False
    assert policy["full_toeformal_aggregate_failed"] is False
    assert policy["full_toeformal_aggregate_timed_out"] is False


def test_phi_transport_consistency_ck_admissibility_rule_closeout_rotates_to_synthesis() -> None:
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
        "PhiTransportConsistencyCKAdmissibilityRuleCloseout.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "PHI_TRANSPORT_CONSISTENCY_CK_ADMISSIBILITY_RULE_CLOSEOUT_20260619_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["closeout_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["admissibility_rule_closeout_prepared"] == "yes"
    assert consumed["third_phi_relevant_ck_admissibility_rule_candidate_closed"] == "yes"
    assert consumed["transport_consistency_rule_candidate_closed"] == "yes"
    assert consumed["three_rule_family_synthesis_packet_authorized"] == "yes"
    assert consumed["three_rule_family_synthesis_packet_prepared"] == "no"
    assert consumed.get("synthesis_packet_prepared", "no") == "no"
    assert consumed["ck_variation_executed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["outcome_id"] == OUTCOME_ID
    assert active_row["closeout_result"] == OUTCOME_ID
    assert active_row["three_rule_family_synthesis_packet_authorized"] == "yes"
    assert active_row["three_rule_family_synthesis_packet_prepared"] == "no"
    assert active_row["synthesis_packet_prepared"] == "no"
    assert active_row["source_admissibility_rule_synthesis_entry_preserved"] == "yes"
    assert active_row["bridge_admissibility_rule_synthesis_entry_preserved"] == "yes"
    assert active_row["transport_consistency_rule_synthesis_entry_preserved"] == "yes"
    assert active_row["another_phi_derivation_selected"] == "no"
    assert active_row["ck_variation_executed"] == "no"
    assert active_row["phi_generated_by_ck_claimed"] == "no"
    assert active_row["potential_derived"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"
    assert active_row["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"


def test_phi_transport_consistency_ck_admissibility_rule_closeout_mirrors() -> None:
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
        "PhiTransportConsistencyCKAdmissibilityRuleCloseout",
        "CURRENT_LIVE_NEXT_TARGET_v0: prepare_phi_ck_source_bridge_transport_rule_family_synthesis_packet",
        "PHI_TRANSPORT_CONSISTENCY_CK_ADMISSIBILITY_RULE_CLOSEOUT_OUTCOME_v0",
        TRANSPORT_CANDIDATE_ID,
        TRANSPORT_CONSTRAINT_FORM,
        TRANSPORT_CONSTRAINT_EQUATION,
        TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
        SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        "transport-consistency rule candidate",
        "derivation-chain stability rule",
        "admissibility-only",
        "not as an action term",
        "not as a transport proof",
        "not as QFT-GR closure",
        "not as master-action promotion",
        "does not execute C_k variation",
        "no canonical master-action promotion",
        "NOT_RUN",
    ]:
        assert token in joined


def test_phi_transport_consistency_ck_admissibility_rule_closeout_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_phi_transport_consistency_ck_admissibility_rule_closeout_gate.py"
    )
