from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.phi_source_admissibility_ck_admissibility_rule_closeout_report import (
    ADMISSIBILITY_CONSTRAINT_FORM,
    ADMISSIBILITY_ONLY_ROUTE_ID,
    AGGREGATE_TIMEOUT_STATUS,
    ARTIFACT_ID,
    CANDIDATE_CONSTRAINT_EQUATION,
    CANDIDATE_CONSTRAINT_FORM,
    CANDIDATE_CONSTRAINT_ID,
    CLOSEOUT_RESULT,
    CONSUMED_TARGET,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT,
    FIRST_RULE_CLASSIFICATION,
    FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME,
    FUNCTIONAL_EMBEDDING_REVIEW_PATH,
    FUNCTIONAL_EMBEDDING_REVIEW_RESULT,
    LAGRANGE_MULTIPLIER_ACTION_FORM,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_RECOMMENDED_CK_FAMILY,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    ON_SHELL_IMPLICATION_FORM,
    ON_SHELL_RESIDUAL_FORM,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    QUADRATIC_PENALTY_ACTION_FORM,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    RESIDUAL_IDENTITY_FORM,
    SCHEMA_ID,
    SELECTED_CK_CONSTRAINT_FAMILY,
    SELECTED_CK_OPTION_CLASS,
    build_phi_source_admissibility_ck_admissibility_rule_closeout,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "phi_source_admissibility_ck_admissibility_rule_closeout_report.py"
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


def test_phi_source_admissibility_ck_admissibility_rule_closeout_files_exist() -> None:
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


def test_phi_source_admissibility_ck_admissibility_rule_closeout_accepts_review() -> None:
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
    assert build_phi_source_admissibility_ck_admissibility_rule_closeout() == closeout


def test_phi_source_admissibility_ck_admissibility_rule_closeout_preserves_forms() -> None:
    closeout = _json(DEFAULT_OUT)
    assert closeout["selected_ck_option_class"] == SELECTED_CK_OPTION_CLASS
    assert closeout["selected_ck_constraint_family"] == SELECTED_CK_CONSTRAINT_FAMILY
    assert (
        closeout["first_phi_relevant_ck_admissibility_rule_candidate_classification"]
        == FIRST_RULE_CLASSIFICATION
    )
    assert closeout["candidate_constraint_id"] == CANDIDATE_CONSTRAINT_ID
    assert closeout["candidate_constraint_form"] == CANDIDATE_CONSTRAINT_FORM
    assert closeout["candidate_constraint_equation"] == CANDIDATE_CONSTRAINT_EQUATION
    assert closeout["admissibility_constraint_form"] == ADMISSIBILITY_CONSTRAINT_FORM
    assert closeout["on_shell_residual_form"] == ON_SHELL_RESIDUAL_FORM
    assert closeout["residual_identity_form"] == RESIDUAL_IDENTITY_FORM
    assert closeout["on_shell_implication_form"] == ON_SHELL_IMPLICATION_FORM
    assert closeout["selected_embedding_route_id"] == ADMISSIBILITY_ONLY_ROUTE_ID
    assert closeout["lagrange_multiplier_action_form"] == LAGRANGE_MULTIPLIER_ACTION_FORM
    assert closeout["quadratic_penalty_action_form"] == QUADRATIC_PENALTY_ACTION_FORM


def test_phi_source_admissibility_ck_admissibility_rule_closeout_records_required_points() -> None:
    closeout = _json(DEFAULT_OUT)
    assert closeout["closeout_criteria_count"] == 11
    assert closeout["closeout_criteria_accepted_count"] == 11
    assert {row["row_id"] for row in closeout["closeout_criteria"]} == {
        "functional_embedding_review_accepts_admissibility_only",
        "first_phi_relevant_ck_rule_candidate_closed",
        "conservation_residual_form_preserved",
        "admissibility_condition_preserved",
        "scalar_residual_identity_preserved",
        "not_action_term_or_dynamical_law",
        "multiplier_and_penalty_routes_remain_blocked",
        "no_variation_generation_or_potential_derivation",
        "no_new_conservation_or_source_proof",
        "no_closure_promotion_or_empirical_claim",
        "next_family_selector_authorized",
    }
    assert closeout["admissibility_rule_closeout_prepared"] is True
    assert closeout["admissibility_rule_closeout_accepted"] is True
    assert closeout["first_phi_relevant_ck_admissibility_rule_candidate_closed"] is True
    assert closeout["source_admissibility_rule_candidate_closed"] is True
    assert closeout["admissibility_only_route_selected"] is True
    assert closeout["constraint_as_admissibility_rule_selected"] is True
    assert closeout["candidate_recorded_as_rule_only"] is True
    assert closeout["source_admissibility_family_closed_as_candidate_only"] is True
    assert closeout["next_selector_authorized"] is True
    assert closeout["next_selector_prepared"] is False
    assert closeout["next_candidate_family_recommendation"] == NEXT_RECOMMENDED_CK_FAMILY
    assert closeout["next_candidate_family_selected"] is False
    assert closeout["bridge_admissibility_family_selected"] is False


def test_phi_source_admissibility_ck_admissibility_rule_closeout_blocks_shortcuts() -> None:
    closeout = _json(DEFAULT_OUT)
    for key in [
        "constraint_as_action_term_selected",
        "dynamical_action_embedding_selected",
        "candidate_recorded_as_new_physical_law",
        "candidate_recorded_as_action_term",
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
        "ck_action_embedding_claimed",
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
    assert "first phi-relevant C_k admissibility rule candidate only" in (
        closeout["non_claim_boundary"]
    )
    assert "not as an action term" in closeout["non_claim_boundary"]
    assert "not as a new dynamical law" in closeout["non_claim_boundary"]
    assert "does not execute C_k variation" in closeout["non_claim_boundary"]
    assert "does not prove new conservation" in closeout["non_claim_boundary"]
    assert "bridge-admissibility family is recommended only" in (
        closeout["non_claim_boundary"]
    )


def test_phi_source_admissibility_ck_admissibility_rule_closeout_validation_policy() -> None:
    closeout = _json(DEFAULT_OUT)
    policy = closeout["validation_policy"]
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["aggregate_lean_validation_status_for_packet"] == (
        AGGREGATE_TIMEOUT_STATUS
    )
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False


def test_phi_source_admissibility_ck_admissibility_rule_closeout_rotates_to_selector() -> None:
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
        "PhiSourceAdmissibilityCKAdmissibilityRuleCloseout.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "PHI_SOURCE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSEOUT_20260618_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["closeout_result"] == OUTCOME_ID
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["admissibility_rule_closeout_prepared"] == "yes"
    assert consumed["first_phi_relevant_ck_admissibility_rule_candidate_closed"] == "yes"
    assert consumed["ck_variation_executed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["authorized_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["outcome_id"] == OUTCOME_ID
    assert active_row["closeout_result"] == OUTCOME_ID
    assert active_row["next_selector_authorized"] == "yes"
    assert active_row["next_selector_prepared"] == "no"
    assert active_row["next_candidate_family_recommendation"] == NEXT_RECOMMENDED_CK_FAMILY
    assert active_row["next_candidate_family_selected"] == "no"
    assert active_row["bridge_admissibility_family_selected"] == "no"
    assert active_row["ck_variation_executed"] == "no"
    assert active_row["phi_generated_by_ck_claimed"] == "no"
    assert active_row["potential_derived"] == "no"
    assert active_row["new_conservation_proof_claimed"] == "no"
    assert active_row["new_source_admissibility_proof_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"
    assert active_row["master_action_promoted"] == "no"


def test_phi_source_admissibility_ck_admissibility_rule_closeout_mirrors() -> None:
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
        "PhiSourceAdmissibilityCKAdmissibilityRuleCloseout",
        "CURRENT_LIVE_NEXT_TARGET_v0: select_next_phi_relevant_ck_constraint_family_after_source_admissibility",
        CANDIDATE_CONSTRAINT_ID,
        CANDIDATE_CONSTRAINT_FORM,
        CANDIDATE_CONSTRAINT_EQUATION,
        ADMISSIBILITY_CONSTRAINT_FORM,
        ON_SHELL_RESIDUAL_FORM,
        RESIDUAL_IDENTITY_FORM,
        "first phi-relevant C_k admissibility rule candidate",
        "not as an action term",
        "not as a new dynamical law",
        "does not execute C_k variation",
        "does not prove new conservation",
        "bridge-admissibility family is recommended only",
        "no QFT-GR closure",
        "no canonical master-action promotion",
        "INCOMPLETE_TIMEOUT_STEADY_PROGRESS",
    ]:
        assert token in joined


def test_phi_source_admissibility_ck_admissibility_rule_closeout_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_phi_source_admissibility_ck_admissibility_rule_closeout_gate.py"
    )
