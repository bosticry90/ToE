from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.phi_bridge_admissibility_ck_admissibility_rule_closeout_report import (
    ADMISSIBILITY_ONLY_ROUTE_ID,
    AGGREGATE_TIMEOUT_STATUS,
    ARTIFACT_ID,
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_CANDIDATE_ID,
    BRIDGE_CANDIDATE_RULE_PLAIN_MEANING,
    BRIDGE_CANDIDATE_TYPE,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
    BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
    BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
    BRIDGE_RULE_CLASSIFICATION,
    BRIDGE_RULE_EPISTEMIC_STATUS,
    CLOSEOUT_RESULT,
    CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME,
    FUNCTIONAL_EMBEDDING_REVIEW_PATH,
    FUNCTIONAL_EMBEDDING_REVIEW_RESULT,
    LAGRANGE_MULTIPLIER_ACTION_FORM,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PENALTY_ACTION_FORM,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID,
    SECOND_RULE_CLASSIFICATION,
    SELECTED_CK_CONSTRAINT_FAMILY,
    SELECTED_CK_OPTION_CLASS,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    SOURCE_RULE_CLOSEOUT_OUTCOME,
    build_phi_bridge_admissibility_ck_admissibility_rule_closeout,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "phi_bridge_admissibility_ck_admissibility_rule_closeout_report.py"
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


def test_phi_bridge_admissibility_ck_admissibility_rule_closeout_files_exist() -> None:
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


def test_phi_bridge_admissibility_ck_admissibility_rule_closeout_accepts_review() -> None:
    review = _json(FUNCTIONAL_EMBEDDING_REVIEW_PATH)
    closeout = _json(DEFAULT_OUT)
    assert review["outcome_id"] == FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME
    assert review["review_result"] == FUNCTIONAL_EMBEDDING_REVIEW_RESULT
    assert closeout["artifact_id"] == ARTIFACT_ID
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
    assert closeout["functional_embedding_review_outcome"] == (
        FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME
    )
    assert closeout["functional_embedding_review_result"] == (
        FUNCTIONAL_EMBEDDING_REVIEW_RESULT
    )
    assert build_phi_bridge_admissibility_ck_admissibility_rule_closeout() == closeout


def test_phi_bridge_admissibility_ck_admissibility_rule_closeout_preserves_forms() -> None:
    closeout = _json(DEFAULT_OUT)
    assert closeout["selected_ck_option_class"] == SELECTED_CK_OPTION_CLASS
    assert closeout["selected_ck_constraint_family"] == SELECTED_CK_CONSTRAINT_FAMILY
    assert (
        closeout["second_phi_relevant_ck_admissibility_rule_candidate_classification"]
        == SECOND_RULE_CLASSIFICATION
    )
    assert closeout["bridge_rule_classification"] == BRIDGE_RULE_CLASSIFICATION
    assert closeout["bridge_rule_epistemic_status"] == BRIDGE_RULE_EPISTEMIC_STATUS
    assert closeout["bridge_candidate_id"] == BRIDGE_CANDIDATE_ID
    assert closeout["bridge_candidate_type"] == BRIDGE_CANDIDATE_TYPE
    assert closeout["bridge_constraint_form"] == BRIDGE_CONSTRAINT_FORM
    assert closeout["bridge_constraint_equation"] == BRIDGE_CONSTRAINT_EQUATION
    assert closeout["bridge_admissibility_constraint_form"] == (
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert closeout["bridge_route_field_equation_match"] == (
        BRIDGE_ROUTE_FIELD_EQUATION_MATCH
    )
    assert closeout["bridge_route_stress_energy_match"] == (
        BRIDGE_ROUTE_STRESS_ENERGY_MATCH
    )
    assert closeout["bridge_route_source_residual_match"] == (
        BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH
    )
    assert closeout["bridge_candidate_rule_plain_meaning"] == (
        BRIDGE_CANDIDATE_RULE_PLAIN_MEANING
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
    assert closeout["selected_embedding_route_id"] == ADMISSIBILITY_ONLY_ROUTE_ID
    assert closeout["lagrange_multiplier_action_form"] == LAGRANGE_MULTIPLIER_ACTION_FORM
    assert closeout["penalty_action_form"] == PENALTY_ACTION_FORM


def test_phi_bridge_admissibility_ck_admissibility_rule_closeout_records_points() -> None:
    closeout = _json(DEFAULT_OUT)
    assert closeout["closeout_criteria_count"] == 12
    assert closeout["closeout_criteria_accepted_count"] == 12
    assert {row["row_id"] for row in closeout["closeout_criteria"]} == {
        "functional_embedding_review_accepts_admissibility_only",
        "second_phi_relevant_ck_rule_candidate_closed",
        "bridge_tuple_preserved",
        "bridge_condition_preserved",
        "bridge_components_preserved",
        "source_rule_context_preserved",
        "closed_as_bridge_admissibility_rule_candidate",
        "not_action_term_or_native_generation_theorem",
        "multiplier_and_penalty_routes_remain_blocked",
        "no_variation_generation_or_potential_derivation",
        "no_bridge_proof_qft_gr_closure_or_master_promotion",
        "phi_ck_rule_family_synthesis_packet_authorized",
    }
    assert closeout["admissibility_rule_closeout_prepared"] is True
    assert closeout["admissibility_rule_closeout_accepted"] is True
    assert closeout["second_phi_relevant_ck_admissibility_rule_candidate_closed"] is True
    assert closeout["bridge_admissibility_rule_candidate_closed"] is True
    assert closeout["bridge_admissibility_rule_closed_as_route_consistency_rule"] is True
    assert closeout["route_consistency_rule_candidate_closed"] is True
    assert closeout["admissibility_only_route_selected"] is True
    assert closeout["constraint_as_admissibility_rule_selected"] is True
    assert closeout["candidate_recorded_as_rule_only"] is True
    assert closeout["route_consistency_tuple_carried_forward"] is True
    assert closeout["field_equation_match_component_preserved"] is True
    assert closeout["stress_energy_match_component_preserved"] is True
    assert closeout["source_residual_match_component_preserved"] is True
    assert closeout["source_admissibility_context_preserved"] is True
    assert closeout["rule_family_synthesis_packet_authorized"] is True
    assert closeout["rule_family_synthesis_packet_prepared"] is False
    assert closeout["phi_ck_admissibility_rule_family_contains_count"] == 2
    assert closeout["source_admissibility_rule_synthesis_entry_preserved"] is True
    assert closeout["bridge_admissibility_rule_synthesis_entry_preserved"] is True
    assert closeout["another_phi_derivation_selected"] is False


def test_phi_bridge_admissibility_ck_admissibility_rule_closeout_blocks_shortcuts() -> None:
    closeout = _json(DEFAULT_OUT)
    for key in [
        "constraint_as_action_term_selected",
        "dynamical_action_embedding_selected",
        "candidate_recorded_as_new_physical_law",
        "candidate_recorded_as_action_term",
        "bridge_candidate_recorded_as_action_term",
        "bridge_candidate_recorded_as_new_dynamical_law",
        "penalty_route_licensed",
        "transport_consistency_family_selected",
        "master_action_surface_rotation_selected",
        "qft_gr_semiclassical_prerequisite_return_selected",
        "public_explanatory_section_selected",
        "bridge_functional_selected",
        "bridge_candidate_functional_defined",
        "bridge_candidate_functional_selected",
        "component_pairing_rule_selected",
        "multiplier_component_domain_selected",
        "constraint_multiplier_type_selected",
        "constraint_term_selected",
        "multiplier_type_selected",
        "multiplier_domain_selected",
        "covariance_of_multiplier_pairing_established",
        "boundary_terms_controlled",
        "variation_policy_for_embedding_selected",
        "fully_concrete_ck_functional_selected",
        "fully_concrete_ck_functional_defined",
        "concrete_ck_functional_selected",
        "concrete_ck_functional_defined",
        "ck_functional_formula_fully_defined",
        "ck_functional_formula_selected",
        "candidate_action_insertion_executed",
        "ck_variation_executed",
        "ck_variation_authorized",
        "lambda_variation_executed",
        "metric_variation_of_candidate_executed",
        "phi_variation_of_candidate_executed",
        "penalty_variation_executed",
        "ck_family_claimed_as_physical_law",
        "ck_action_embedding_claimed",
        "bridge_candidate_rule_proved",
        "bridge_admissibility_claimed",
        "bridge_admissibility_proved",
        "bridge_route_alignment_verified",
        "route_consistency_tuple_proved",
        "field_equation_match_proved",
        "stress_energy_match_proved",
        "source_residual_match_proved",
        "phi_generated_by_ck_claimed",
        "phi_generation_theorem_claimed",
        "derived_v_phi_claimed",
        "v_phi_derivation_claimed",
        "potential_derived",
        "new_conservation_proof_claimed",
        "new_source_admissibility_proof_claimed",
        "source_admissibility_claimed",
        "source_admissibility_completed",
        "source_conservation_claimed",
        "weak_conservation_claimed",
        "bianchi_compatibility_claimed",
        "qft_gr_closure_claimed",
        "qft_gr_solved",
        "qft_gr_seam_closed",
        "qft_gr_source_map_closure_authorized",
        "semiclassical_coupling_authorized",
        "semiclassical_coupling_claimed",
        "semiclassical_einstein_equation_derived",
        "semiclassical_source_established",
        "master_action_promoted",
        "master_action_promotion_authorized",
        "canonical_master_action_promoted",
        "toe_native_matter_derivation_claimed",
        "toe_native_matter_sector_derived",
        "toe_native_matter_sector_defined",
        "standard_model_derivation_claimed",
        "native_generation_theorem_claimed",
        "empirical_validation_claimed",
        "public_readiness_claimed",
        "phase2_readiness_claim",
        "pillar_completion_inferred",
        "seam_closure_claim",
    ]:
        assert closeout[key] is False, key
    assert "second phi-relevant C_k admissibility rule candidate only" in (
        closeout["non_claim_boundary"]
    )
    assert "not as an action term" in closeout["non_claim_boundary"]
    assert "not as a native-generation theorem" in closeout["non_claim_boundary"]
    assert "not as QFT-GR closure" in closeout["non_claim_boundary"]
    assert "not as master-action promotion" in closeout["non_claim_boundary"]
    assert "does not execute C_k variation" in closeout["non_claim_boundary"]
    assert "not another immediate phi derivation" in closeout["non_claim_boundary"]


def test_phi_bridge_admissibility_ck_admissibility_rule_closeout_validation_policy() -> None:
    closeout = _json(DEFAULT_OUT)
    policy = closeout["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == (
        AGGREGATE_TIMEOUT_STATUS
    )
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_phi_bridge_admissibility_ck_admissibility_rule_closeout_rotates_to_synthesis() -> None:
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
        "PhiBridgeAdmissibilityCKAdmissibilityRuleCloseout.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "PHI_BRIDGE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSEOUT_20260619_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["closeout_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["admissibility_rule_closeout_prepared"] == "yes"
    assert (
        consumed["second_phi_relevant_ck_admissibility_rule_candidate_closed"]
        == "yes"
    )
    assert consumed["bridge_admissibility_rule_candidate_closed"] == "yes"
    assert consumed["rule_family_synthesis_packet_authorized"] == "yes"
    assert consumed["rule_family_synthesis_packet_prepared"] == "no"
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
    assert active_row["rule_family_synthesis_packet_authorized"] == "yes"
    assert active_row["rule_family_synthesis_packet_prepared"] == "no"
    assert active_row["source_admissibility_rule_synthesis_entry_preserved"] == "yes"
    assert active_row["bridge_admissibility_rule_synthesis_entry_preserved"] == "yes"
    assert active_row["another_phi_derivation_selected"] == "no"
    assert active_row["ck_variation_executed"] == "no"
    assert active_row["phi_generated_by_ck_claimed"] == "no"
    assert active_row["potential_derived"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_phi_bridge_admissibility_ck_admissibility_rule_closeout_mirrors() -> None:
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
        "PhiBridgeAdmissibilityCKAdmissibilityRuleCloseout",
        "CURRENT_LIVE_NEXT_TARGET_v0: prepare_phi_ck_admissibility_rule_family_synthesis_packet",
        BRIDGE_CANDIDATE_ID,
        BRIDGE_CONSTRAINT_FORM,
        BRIDGE_CONSTRAINT_EQUATION,
        BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
        BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
        BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        "bridge-admissibility rule candidate",
        "admissibility-only",
        "not as an action term",
        "not as a native-generation theorem",
        "not as QFT-GR closure",
        "not as master-action promotion",
        "does not execute C_k variation",
        "not another immediate phi derivation",
        "no canonical master-action promotion",
        "INCOMPLETE_TIMEOUT_STEADY_PROGRESS",
    ]:
        assert token in joined


def test_phi_bridge_admissibility_ck_admissibility_rule_closeout_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_phi_bridge_admissibility_ck_admissibility_rule_closeout_gate.py"
    )
