from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.phi_source_admissibility_ck_functional_embedding_packet_report import (
    DEFAULT_OUT as EMBEDDING_PACKET_PATH,
    OUTCOME_ID as EMBEDDING_PACKET_OUTCOME,
    PACKET_RESULT as EMBEDDING_PACKET_RESULT,
)
from formal.python.tools.phi_source_admissibility_ck_functional_embedding_packet_result_review_report import (
    ADMISSIBILITY_CONSTRAINT_FORM,
    ADMISSIBILITY_ONLY_ROUTE_ID,
    AGGREGATE_TIMEOUT_STATUS,
    ARTIFACT_ID,
    CANDIDATE_CONSTRAINT_EQUATION,
    CANDIDATE_CONSTRAINT_FORM,
    CANDIDATE_CONSTRAINT_ID,
    CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    DIRECT_DIVERGENCE_INSERTION_FORM,
    FIRST_RULE_CLASSIFICATION,
    LAGRANGE_MULTIPLIER_ACTION_FORM,
    LAGRANGE_MULTIPLIER_ROUTE_ID,
    LAGRANGE_MULTIPLIER_ROUTE_STATUS,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    ON_SHELL_IMPLICATION_FORM,
    ON_SHELL_RESIDUAL_FORM,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    QUADRATIC_PENALTY_ACTION_FORM,
    QUADRATIC_PENALTY_ROUTE_ID,
    QUADRATIC_PENALTY_ROUTE_STATUS,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    RESIDUAL_IDENTITY_FORM,
    REVIEW_RESULT,
    SCHEMA_ID,
    SELECTED_CK_CONSTRAINT_FAMILY,
    SELECTED_CK_OPTION_CLASS,
    WEAK_INTEGRATED_FORM,
    build_phi_source_admissibility_ck_functional_embedding_packet_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "phi_source_admissibility_ck_functional_embedding_packet_result_review_report.py"
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


def test_phi_source_admissibility_ck_functional_embedding_result_review_files_exist() -> None:
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


def test_phi_source_admissibility_ck_functional_embedding_result_review_accepts_packet() -> None:
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
        build_phi_source_admissibility_ck_functional_embedding_packet_result_review()
        == review
    )


def test_phi_source_admissibility_ck_functional_embedding_result_review_carries_forms() -> None:
    review = _json(DEFAULT_OUT)
    assert review["selected_ck_option_class"] == SELECTED_CK_OPTION_CLASS
    assert review["selected_ck_constraint_family"] == SELECTED_CK_CONSTRAINT_FAMILY
    assert review["candidate_constraint_id"] == CANDIDATE_CONSTRAINT_ID
    assert review["candidate_constraint_form"] == CANDIDATE_CONSTRAINT_FORM
    assert review["candidate_constraint_equation"] == CANDIDATE_CONSTRAINT_EQUATION
    assert review["on_shell_residual_form"] == ON_SHELL_RESIDUAL_FORM
    assert review["residual_identity_form"] == RESIDUAL_IDENTITY_FORM
    assert review["on_shell_implication_form"] == ON_SHELL_IMPLICATION_FORM
    assert review["embedding_route_count"] == 3
    assert review["selected_embedding_route_id"] == ADMISSIBILITY_ONLY_ROUTE_ID
    assert review["admissibility_constraint_form"] == ADMISSIBILITY_CONSTRAINT_FORM
    assert review["lagrange_multiplier_route_id"] == LAGRANGE_MULTIPLIER_ROUTE_ID
    assert review["lagrange_multiplier_route_status"] == LAGRANGE_MULTIPLIER_ROUTE_STATUS
    assert review["lagrange_multiplier_action_form"] == LAGRANGE_MULTIPLIER_ACTION_FORM
    assert review["direct_divergence_insertion_form"] == DIRECT_DIVERGENCE_INSERTION_FORM
    assert review["weak_integrated_form"] == WEAK_INTEGRATED_FORM
    assert review["quadratic_penalty_route_id"] == QUADRATIC_PENALTY_ROUTE_ID
    assert review["quadratic_penalty_route_status"] == QUADRATIC_PENALTY_ROUTE_STATUS
    assert review["quadratic_penalty_action_form"] == QUADRATIC_PENALTY_ACTION_FORM


def test_phi_source_admissibility_ck_functional_embedding_result_review_required_points() -> None:
    review = _json(DEFAULT_OUT)
    assert review["review_criteria_count"] == 11
    assert review["review_criteria_accepted_count"] == 11
    assert {row["row_id"] for row in review["review_criteria"]} == {
        "admissibility_only_route_selected",
        "multiplier_action_route_blocked",
        "quadratic_penalty_route_not_licensed",
        "c_source_zero_preserved_as_rule",
        "conservation_residual_candidate_carried_forward",
        "residual_identity_carried_forward",
        "no_ck_variation_executed",
        "no_phi_generation_or_potential_derivation",
        "no_new_conservation_or_source_proof",
        "no_qft_gr_closure_or_master_action_promotion",
        "admissibility_rule_closeout_next_target_selected",
    }
    assert review["functional_embedding_result_review_prepared"] is True
    assert review["functional_embedding_result_review_accepted"] is True
    assert review["review_accepts_admissibility_only_route"] is True
    assert review["packet_result_review_accepts_admissibility_only_route"] is True
    assert review["admissibility_rule_closeout_authorized"] is True
    assert review["admissibility_rule_closeout_prepared"] is False
    assert (
        review["first_phi_relevant_ck_admissibility_rule_candidate_classification"]
        == FIRST_RULE_CLASSIFICATION
    )


def test_phi_source_admissibility_ck_functional_embedding_result_review_blocks_shortcuts() -> None:
    review = _json(DEFAULT_OUT)
    assert review["functional_embedding_packet_prepared"] is True
    assert review["functional_embedding_options_recorded"] is True
    assert review["admissibility_only_route_selected"] is True
    assert review["constraint_as_admissibility_rule_selected"] is True
    assert review["lagrange_multiplier_route_recorded"] is True
    assert review["lagrange_multiplier_route_blocked"] is True
    assert review["quadratic_penalty_route_recorded"] is True
    for key in [
        "dynamical_action_embedding_selected",
        "constraint_as_action_term_selected",
        "weak_integrated_form_boundary_controlled",
        "quadratic_penalty_route_licensed",
        "constraint_multiplier_type_selected",
        "constraint_term_selected",
        "lambda_nu_domain_selected",
        "lambda_nu_variational_role_selected",
        "higher_derivative_scope_resolved",
        "boundary_terms_controlled",
        "regularity_domain_of_c_source_defined_for_action_embedding",
        "covariance_of_lambda_c_source_established",
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
        "quadratic_penalty_variation_executed",
        "ck_family_claimed_as_physical_law",
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
        assert review[key] is False, key
    assert "accepts the admissibility-only route as a rule only" in (
        review["non_claim_boundary"]
    )
    assert "not as an action term" in review["non_claim_boundary"]
    assert "keeps the multiplier/action route blocked" in review["non_claim_boundary"]
    assert "keeps the quadratic penalty route not licensed" in (
        review["non_claim_boundary"]
    )
    assert "does not execute C_k variation" in review["non_claim_boundary"]
    assert "no source admissibility or conservation" in review["non_claim_boundary"]
    assert "no QFT-GR closure" in review["non_claim_boundary"]


def test_phi_source_admissibility_ck_functional_embedding_result_review_validation_policy() -> None:
    review = _json(DEFAULT_OUT)
    policy = review["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == (
        AGGREGATE_TIMEOUT_STATUS
    )
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_phi_source_admissibility_ck_functional_embedding_result_review_rotates_to_closeout() -> None:
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
        "PhiSourceAdmissibilityCKFunctionalEmbeddingPacketResultReview.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "PHI_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW_"
        "20260618_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["admissibility_only_route_selected"] == "yes"
    assert consumed["constraint_as_admissibility_rule_selected"] == "yes"
    assert consumed["lagrange_multiplier_route_blocked"] == "yes"
    assert consumed["quadratic_penalty_route_licensed"] == "no"
    assert consumed["ck_variation_executed"] == "no"
    assert consumed["source_admissibility_claimed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["review_result"] == OUTCOME_ID
    assert active_row["admissibility_rule_closeout_authorized"] == "yes"
    assert active_row["admissibility_rule_closeout_prepared"] == "no"
    assert active_row["admissibility_only_route_selected"] == "yes"
    assert active_row["constraint_as_admissibility_rule_selected"] == "yes"
    assert active_row["constraint_as_action_term_selected"] == "no"
    assert active_row["lagrange_multiplier_route_blocked"] == "yes"
    assert active_row["quadratic_penalty_route_licensed"] == "no"
    assert active_row["ck_variation_executed"] == "no"
    assert active_row["phi_generated_by_ck_claimed"] == "no"
    assert active_row["potential_derived"] == "no"
    assert active_row["source_admissibility_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_phi_source_admissibility_ck_functional_embedding_result_review_mirrors() -> None:
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
        "PhiSourceAdmissibilityCKFunctionalEmbeddingPacketResultReview",
        "CURRENT_LIVE_NEXT_TARGET_v0: prepare_phi_source_admissibility_ck_admissibility_rule_closeout",
        CANDIDATE_CONSTRAINT_ID,
        CANDIDATE_CONSTRAINT_FORM,
        CANDIDATE_CONSTRAINT_EQUATION,
        ON_SHELL_RESIDUAL_FORM,
        RESIDUAL_IDENTITY_FORM,
        ADMISSIBILITY_CONSTRAINT_FORM,
        LAGRANGE_MULTIPLIER_ACTION_FORM,
        QUADRATIC_PENALTY_ACTION_FORM,
        "accepts the admissibility-only route as a rule only",
        "not as an action term",
        "keeps the multiplier/action route blocked",
        "keeps the quadratic penalty route not licensed",
        "does not select or define a fully concrete C_k functional",
        "C_k remains inactive and undefined",
        "V(phi) remains smooth bounded-below but not derived",
        "C_k does not yet generate phi",
        "no ToE-native matter derivation",
        "no native-generation theorem",
        "no source admissibility or conservation",
        "no QFT-GR closure",
        "no canonical master-action promotion",
        "INCOMPLETE_TIMEOUT_STEADY_PROGRESS",
    ]:
        assert token in joined


def test_phi_source_admissibility_ck_functional_embedding_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_phi_source_admissibility_ck_functional_embedding_packet_result_review_gate.py"
    )
