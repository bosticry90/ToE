from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.phi_transport_consistency_ck_functional_embedding_packet_report import (
    DEFAULT_OUT as EMBEDDING_PACKET_PATH,
    OUTCOME_ID as EMBEDDING_PACKET_OUTCOME,
    PACKET_RESULT as EMBEDDING_PACKET_RESULT,
)
from formal.python.tools.phi_transport_consistency_ck_functional_embedding_packet_result_review_report import (
    ADMISSIBILITY_ONLY_ROUTE_ID,
    ADMISSIBILITY_ONLY_ROUTE_STATUS,
    ARTIFACT_ID,
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    DIRECT_DYNAMICAL_LAW_INTERPRETATION_ID,
    DIRECT_DYNAMICAL_LAW_INTERPRETATION_STATUS,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    KNOWN_PHI_TRANSPORT_CHAIN_FORM,
    LAGRANGE_MULTIPLIER_ACTION_FORM,
    LAGRANGE_MULTIPLIER_ROUTE_ID,
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
    PENALTY_ROUTE_ID,
    PENALTY_ROUTE_STATUS,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    REVIEW_RESULT,
    SCHEMA_ID,
    SELECTED_CK_CONSTRAINT_FAMILY,
    SELECTED_CK_OPTION_CLASS,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    THIRD_RULE_CLASSIFICATION,
    TRANSPORT_ACTION_EMBEDDING_CHAIN_FORM,
    TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
    TRANSPORT_CANDIDATE_ID,
    TRANSPORT_CANDIDATE_TYPE,
    TRANSPORT_COMPONENTS,
    TRANSPORT_CONSTRAINT_EQUATION,
    TRANSPORT_CONSTRAINT_FORM,
    TRANSPORT_MULTIPLIER_BLOCKING_REASONS,
    TRANSPORT_PENALTY_BLOCKING_REASONS,
    TRANSPORT_RULE_CLASSIFICATION,
    TRANSPORT_RULE_EPISTEMIC_STATUS,
    build_phi_transport_consistency_ck_functional_embedding_packet_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "phi_transport_consistency_ck_functional_embedding_packet_result_review_report.py"
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


def test_phi_transport_consistency_ck_functional_embedding_result_review_files_exist() -> None:
    for path in [
        EMBEDDING_PACKET_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_phi_transport_consistency_ck_functional_embedding_result_review_accepts_packet() -> None:
    packet = _json(EMBEDDING_PACKET_PATH)
    review = _json(DEFAULT_OUT)
    assert packet["outcome_id"] == EMBEDDING_PACKET_OUTCOME
    assert packet["packet_result"] == EMBEDDING_PACKET_RESULT
    assert review["artifact_id"] == ARTIFACT_ID
    assert review["schema_id"] == SCHEMA_ID
    assert review["packet_id"] == PACKET_ID
    assert review["prepared"] is True
    assert review["accepted"] is True
    assert review["review_prepared"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["review_result"] == REVIEW_RESULT
    assert review["packet_classification"] == PACKET_CLASSIFICATION
    assert review["consumed_target"] == CONSUMED_TARGET
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["embedding_packet_outcome"] == EMBEDDING_PACKET_OUTCOME
    assert review["embedding_packet_result"] == EMBEDDING_PACKET_RESULT
    assert (
        build_phi_transport_consistency_ck_functional_embedding_packet_result_review()
        == review
    )


def test_phi_transport_consistency_ck_functional_embedding_result_review_carries_forms() -> None:
    review = _json(DEFAULT_OUT)
    assert review["selected_ck_option_class"] == SELECTED_CK_OPTION_CLASS
    assert review["selected_ck_constraint_family"] == SELECTED_CK_CONSTRAINT_FAMILY
    assert review["transport_candidate_id"] == TRANSPORT_CANDIDATE_ID
    assert review["transport_candidate_type"] == TRANSPORT_CANDIDATE_TYPE
    assert review["transport_rule_classification"] == TRANSPORT_RULE_CLASSIFICATION
    assert review["transport_rule_epistemic_status"] == TRANSPORT_RULE_EPISTEMIC_STATUS
    assert review["transport_constraint_form"] == TRANSPORT_CONSTRAINT_FORM
    assert review["transport_constraint_equation"] == TRANSPORT_CONSTRAINT_EQUATION
    assert (
        review["transport_admissibility_constraint_form"]
        == TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert review["transport_component_count"] == len(TRANSPORT_COMPONENTS)
    assert review["transport_component_forms"] == [
        row["component_form"] for row in TRANSPORT_COMPONENTS
    ]
    assert review["transport_action_embedding_chain_form"] == (
        TRANSPORT_ACTION_EMBEDDING_CHAIN_FORM
    )
    assert review["known_phi_transport_chain_form"] == KNOWN_PHI_TRANSPORT_CHAIN_FORM
    assert review["source_candidate_constraint_id"] == SOURCE_CANDIDATE_CONSTRAINT_ID
    assert review["source_candidate_constraint_form"] == SOURCE_CANDIDATE_CONSTRAINT_FORM
    assert review["source_candidate_constraint_equation"] == (
        SOURCE_CANDIDATE_CONSTRAINT_EQUATION
    )
    assert review["source_admissibility_constraint_form"] == (
        SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert review["bridge_constraint_form"] == BRIDGE_CONSTRAINT_FORM
    assert review["bridge_constraint_equation"] == BRIDGE_CONSTRAINT_EQUATION
    assert review["bridge_admissibility_constraint_form"] == (
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert review["closed_phi_ck_rule_roles"] == [
        "source admissibility",
        "bridge admissibility",
        "transport consistency",
    ]
    assert review["embedding_route_count"] == 3
    assert review["selected_embedding_route_id"] == ADMISSIBILITY_ONLY_ROUTE_ID
    assert review["admissibility_only_route_status"] == ADMISSIBILITY_ONLY_ROUTE_STATUS
    assert review["lagrange_multiplier_route_id"] == LAGRANGE_MULTIPLIER_ROUTE_ID
    assert review["lagrange_multiplier_route_status"] == LAGRANGE_MULTIPLIER_ROUTE_STATUS
    assert review["lagrange_multiplier_action_form"] == LAGRANGE_MULTIPLIER_ACTION_FORM
    assert review["penalty_route_id"] == PENALTY_ROUTE_ID
    assert review["penalty_route_status"] == PENALTY_ROUTE_STATUS
    assert review["penalty_action_form"] == PENALTY_ACTION_FORM
    assert review["direct_dynamical_law_interpretation_id"] == (
        DIRECT_DYNAMICAL_LAW_INTERPRETATION_ID
    )
    assert review["direct_dynamical_law_interpretation_status"] == (
        DIRECT_DYNAMICAL_LAW_INTERPRETATION_STATUS
    )
    assert review["transport_multiplier_blocking_reasons"] == (
        TRANSPORT_MULTIPLIER_BLOCKING_REASONS
    )
    assert review["transport_penalty_blocking_reasons"] == (
        TRANSPORT_PENALTY_BLOCKING_REASONS
    )


def test_phi_transport_consistency_ck_functional_embedding_result_review_required_points() -> None:
    review = _json(DEFAULT_OUT)
    assert review["review_criteria_count"] == 14
    assert review["review_criteria_accepted_count"] == 14
    assert {row["row_id"] for row in review["review_criteria"]} == {
        "admissibility_only_route_selected",
        "c_transport_zero_preserved_as_rule",
        "transport_tuple_carried_forward",
        "transport_components_carried_forward",
        "source_and_bridge_context_preserved",
        "multiplier_action_route_blocked",
        "penalty_route_not_licensed",
        "direct_dynamical_law_interpretation_blocked",
        "no_ck_variation_or_action_embedding",
        "no_transport_proof_or_route_alignment_proof",
        "no_phi_generation_or_potential_derivation",
        "no_qft_gr_closure_or_master_action_promotion",
        "full_toeformal_aggregate_recorded_not_run",
        "transport_admissibility_rule_closeout_next_target_selected",
    }
    assert review["functional_embedding_result_review_prepared"] is True
    assert review["functional_embedding_result_review_accepted"] is True
    assert review["review_accepts_admissibility_only_route"] is True
    assert review["packet_result_review_accepts_admissibility_only_route"] is True
    assert review["transport_admissibility_rule_closeout_authorized"] is True
    assert review["transport_admissibility_rule_closeout_prepared"] is False
    assert (
        review["third_phi_relevant_ck_admissibility_rule_candidate_classification"]
        == THIRD_RULE_CLASSIFICATION
    )


def test_phi_transport_consistency_ck_functional_embedding_result_review_blocks_shortcuts() -> None:
    review = _json(DEFAULT_OUT)
    assert review["functional_embedding_packet_prepared"] is True
    assert review["functional_embedding_options_recorded"] is True
    assert review["admissibility_only_route_selected"] is True
    assert review["constraint_as_admissibility_rule_selected"] is True
    assert review["lagrange_multiplier_route_recorded"] is True
    assert review["lagrange_multiplier_route_blocked"] is True
    assert review["penalty_route_recorded"] is True
    assert review["penalty_would_change_dynamics"] is True
    assert review["direct_dynamical_law_interpretation_recorded"] is True
    assert review["direct_dynamical_law_interpretation_blocked"] is True
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
        "direct_dynamical_law_interpretation_selected",
        "heterogeneous_tuple_norm_defined",
        "fully_concrete_ck_functional_selected",
        "fully_concrete_ck_functional_defined",
        "concrete_ck_functional_selected",
        "concrete_ck_functional_defined",
        "ck_functional_formula_fully_defined",
        "ck_functional_formula_selected",
        "ck_action_embedding_claimed",
        "candidate_action_insertion_executed",
        "ck_variation_executed",
        "ck_variation_authorized",
        "lambda_variation_executed",
        "metric_variation_of_candidate_executed",
        "phi_variation_of_candidate_executed",
        "penalty_variation_executed",
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
        "empirical_validation_claimed",
        "public_readiness_claimed",
        "phase2_readiness_claim",
        "seam_closure_claim",
    ]:
        assert review[key] is False, key
    assert "accepts the admissibility-only route as a transport" in (
        review["non_claim_boundary"]
    )
    assert "not as an action term" in review["non_claim_boundary"]
    assert "keeps the multiplier/action route blocked" in review["non_claim_boundary"]
    assert "keeps the penalty route not licensed" in review["non_claim_boundary"]
    assert "keeps direct dynamical-law interpretation blocked" in (
        review["non_claim_boundary"]
    )
    assert "does not execute C_k variation" in review["non_claim_boundary"]
    assert "does not prove transport consistency" in review["non_claim_boundary"]
    assert "does not close QFT-GR" in review["non_claim_boundary"]


def test_phi_transport_consistency_ck_functional_embedding_result_review_validation_policy() -> None:
    review = _json(DEFAULT_OUT)
    policy = review["validation_policy"]
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


def test_phi_transport_consistency_ck_functional_embedding_result_review_rotates_to_closeout() -> None:
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
        "PhiTransportConsistencyCKFunctionalEmbeddingPacketResultReview.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "PHI_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW_"
        "20260619_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["admissibility_only_route_selected"] == "yes"
    assert consumed["lagrange_multiplier_route_blocked"] == "yes"
    assert consumed["penalty_route_licensed"] == "no"
    assert consumed["direct_dynamical_law_interpretation_blocked"] == "yes"
    assert consumed["ck_variation_executed"] == "no"
    assert consumed["transport_consistency_proved"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"
    assert consumed["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["review_result"] == OUTCOME_ID
    assert active_row["transport_admissibility_rule_closeout_authorized"] == "yes"
    assert active_row["transport_admissibility_rule_closeout_prepared"] == "no"
    assert active_row["closeout_prepared"] == "no"
    assert active_row["admissibility_rule_closeout_prepared"] == "no"
    assert active_row["admissibility_only_route_selected"] == "yes"
    assert active_row["constraint_as_admissibility_rule_selected"] == "yes"
    assert active_row["constraint_as_action_term_selected"] == "no"
    assert active_row["lagrange_multiplier_route_blocked"] == "yes"
    assert active_row["penalty_route_licensed"] == "no"
    assert active_row["direct_dynamical_law_interpretation_selected"] == "no"
    assert active_row["ck_variation_executed"] == "no"
    assert active_row["transport_consistency_proved"] == "no"
    assert active_row["phi_generated_by_ck_claimed"] == "no"
    assert active_row["potential_derived"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"
    assert active_row["full_toeformal_aggregate_status_for_packet"] == "NOT_RUN"


def test_phi_transport_consistency_ck_functional_embedding_result_review_mirrors() -> None:
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
        "PhiTransportConsistencyCKFunctionalEmbeddingPacketResultReview",
        (
            "CURRENT_LIVE_NEXT_TARGET_v0: "
            "prepare_phi_transport_consistency_ck_admissibility_rule_closeout"
        ),
        TRANSPORT_CANDIDATE_ID,
        TRANSPORT_CONSTRAINT_FORM,
        TRANSPORT_CONSTRAINT_EQUATION,
        TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
        ADMISSIBILITY_ONLY_ROUTE_ID,
        LAGRANGE_MULTIPLIER_ROUTE_ID,
        PENALTY_ROUTE_ID,
        DIRECT_DYNAMICAL_LAW_INTERPRETATION_ID,
        LAGRANGE_MULTIPLIER_ACTION_FORM,
        PENALTY_ACTION_FORM,
        "accepts the admissibility-only route as a transport",
        "not as an action term",
        "keeps the multiplier/action route blocked",
        "keeps the penalty route not licensed",
        "keeps direct dynamical-law interpretation blocked",
        "does not functionalize C_transport^phi",
        "does not execute C_k variation",
        "does not prove transport consistency",
        "does not prove full route alignment",
        "does not close QFT-GR",
        "no canonical master-action promotion",
        "NOT_RUN",
    ]:
        assert token in joined


def test_phi_transport_consistency_ck_functional_embedding_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_phi_transport_consistency_ck_functional_embedding_packet_result_review_gate.py"
    )
