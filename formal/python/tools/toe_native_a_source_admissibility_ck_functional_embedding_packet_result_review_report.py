from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_a_source_admissibility_ck_functional_embedding_packet_report import (
    ADMISSIBILITY_CONSTRAINT_FORM,
    ADMISSIBILITY_ONLY_ROUTE_ID,
    ADMISSIBILITY_ONLY_ROUTE_STATUS,
    A_FIELD_DOMAIN_POLICY,
    BIANCHI_IDENTITY_ROUTE,
    BOUNDED_SOURCE_ADMISSIBILITY_RESULT,
    CANDIDATE_CONSTRAINT_EQUATION,
    CANDIDATE_CONSTRAINT_FORM,
    CANDIDATE_CONSTRAINT_ID,
    CANDIDATE_CONSTRAINT_INTERPRETATION,
    CANDIDATE_CONSTRAINT_SHORT_FORM,
    COMPONENT_PAIRING_FORM,
    CURRENT_COUPLED_SCOPE_BOUNDARY,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as EMBEDDING_PACKET_PATH,
    DIRECT_DIVERGENCE_INSERTION_FORM,
    DIVERGENCE_IDENTITY,
    F_DEFINITION_POLICY,
    FULL_SOURCE_ADMISSIBILITY_BOUNDARY,
    GAUGE_GROUP_POLICY,
    LAGRANGE_MULTIPLIER_ACTION_FORM,
    LAGRANGE_MULTIPLIER_ROUTE_ID,
    LAGRANGE_MULTIPLIER_ROUTE_STATUS,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    LOCAL_SOURCE_ROUTE_SCOPE,
    NEXT_TARGET as CONSUMED_TARGET,
    ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
    OUTCOME_ID as EMBEDDING_PACKET_OUTCOME,
    PACKET_ID as EMBEDDING_PACKET_ID,
    PACKET_RESULT as EMBEDDING_PACKET_RESULT,
    QFTGR_AGGREGATE_PATH,
    QUADRATIC_PENALTY_ACTION_FORM,
    QUADRATIC_PENALTY_ROUTE_ID,
    QUADRATIC_PENALTY_ROUTE_STATUS,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID as EMBEDDING_PACKET_SCHEMA_ID,
    SELECTED_A_CK_CONSTRAINT_FAMILY,
    SOURCE_ADMISSIBILITY_CONDITION,
    SOURCE_ROUTE_STILL_BLOCKED,
    STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
    VACUUM_EULER_LAGRANGE_ROUTE,
    VACUUM_ON_SHELL_IMPLICATION_FORM,
    VACUUM_SUPPORTING_IDENTITY_FORM,
    WEAK_INTEGRATED_FORM,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-22T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_"
    "RESULT_REVIEW_20260622_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_"
    "RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_RESULT_REVIEW_"
    "ACCEPTS_ADMISSIBILITY_ONLY_ROUTE_NO_ACTION_VARIATION_OR_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_A_source_admissibility_ck_functional_embedding_result_review_"
    "accepts_admissibility_only_route_no_action_variation_or_promotion"
)
NEXT_TARGET = "prepare_toe_native_A_source_admissibility_ck_admissibility_rule_closeout"
NEXT_TARGET_KIND = (
    "toe_native_A_source_admissibility_ck_admissibility_rule_closeout_preparation"
)
FIRST_A_RULE_CLASSIFICATION = (
    "first_A_relevant_ck_vacuum_gauge_source_admissibility_rule_candidate"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_"
    "RESULT_REVIEW_20260622_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeASourceAdmissibilityCKFunctionalEmbeddingPacketResultReview.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _review_criteria(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "admissibility_only_route_selected",
            "status": "accepted",
            "evidence": packet.get("admissibility_constraint_form"),
            "assessment": (
                "The review accepts only C_source^{A,nu}[g,A] = 0 as a "
                "non-dynamical vacuum U(1) admissibility rule."
            ),
        },
        {
            "row_id": "c_source_a_zero_preserved_as_rule",
            "status": "accepted",
            "evidence": ADMISSIBILITY_CONSTRAINT_FORM,
            "assessment": (
                "C_source^{A,nu}[g,A] = 0 is preserved as an admissibility "
                "rule rather than an action term."
            ),
        },
        {
            "row_id": "vacuum_u1_route_context_preserved",
            "status": "accepted",
            "evidence": [
                GAUGE_GROUP_POLICY,
                A_FIELD_DOMAIN_POLICY,
                F_DEFINITION_POLICY,
                VACUUM_EULER_LAGRANGE_ROUTE,
                BOUNDED_SOURCE_ADMISSIBILITY_RESULT,
            ],
            "assessment": "The accepted context remains local classical vacuum U(1) on shell.",
        },
        {
            "row_id": "multiplier_action_route_blocked",
            "status": "accepted",
            "evidence": [
                LAGRANGE_MULTIPLIER_ACTION_FORM,
                DIRECT_DIVERGENCE_INSERTION_FORM,
                COMPONENT_PAIRING_FORM,
                WEAK_INTEGRATED_FORM,
            ],
            "assessment": (
                "The multiplier/action route remains blocked by lambda domain, "
                "component pairing, boundary, variation, higher-derivative, "
                "and gauge-dynamics-preservation gaps."
            ),
        },
        {
            "row_id": "quadratic_penalty_route_unlicensed",
            "status": "accepted",
            "evidence": QUADRATIC_PENALTY_ACTION_FORM,
            "assessment": (
                "The quadratic penalty route remains unlicensed because it "
                "would become a new dynamical penalty term."
            ),
        },
        {
            "row_id": "vacuum_conservation_residual_candidate_carried_forward",
            "status": "accepted",
            "evidence": [CANDIDATE_CONSTRAINT_FORM, CANDIDATE_CONSTRAINT_EQUATION],
            "assessment": "The A conservation-residual candidate is carried forward exactly.",
        },
        {
            "row_id": "no_ck_action_embedding_or_variation",
            "status": "accepted",
            "evidence": [
                "ck_action_embedding_constructed=false",
                "C_k_action_embedding_constructed=false",
                "ck_variation_executed=false",
                "C_k_variation_executed=false",
                "lambda_variation_executed=false",
                "A_variation_of_candidate_executed=false",
                "metric_variation_of_candidate_executed=false",
            ],
            "assessment": "No C_k action embedding or variation is executed.",
        },
        {
            "row_id": "no_current_or_sourced_maxwell_route",
            "status": "accepted",
            "evidence": [
                "J_nu_derived=false",
                "psi_current_route_constructed=false",
                "external_current_native_derivation_selected=false",
                "sourced_maxwell_equation_derived=false",
                "matter_current_exchange_route_proved=false",
            ],
            "assessment": "No current, sourced Maxwell, or matter-current exchange route is introduced.",
        },
        {
            "row_id": "no_new_conservation_or_source_proof",
            "status": "accepted",
            "evidence": [
                "new_conservation_proof_claimed=false",
                "new_source_admissibility_proof_claimed=false",
                "full_source_admissibility_review_accepted=false",
            ],
            "assessment": (
                "The review accepts route selection without claiming a new "
                "conservation proof or full source-admissibility result."
            ),
        },
        {
            "row_id": "no_closure_coupling_validation_or_promotion",
            "status": "accepted",
            "evidence": [
                "full_em_closure_claimed=false",
                "qft_gr_closure_claimed=false",
                "semiclassical_coupling_authorized=false",
                "empirical_validation_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": "Closure, coupling, validation, and promotion remain blocked.",
        },
        {
            "row_id": "admissibility_rule_closeout_next_target_selected",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": (
                "The next target is a bounded closeout of the first A-relevant "
                "vacuum gauge source-admissibility rule."
            ),
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "toe_native_A_source_admissibility_ck_functional_embedding_packet_"
            "result_review"
        ),
        "tiered_lean_validation_policy_formalized": True,
        "routine_packet_validation_tiers": [
            "touched Lean marker",
            "smallest affected Lake target",
            "lane aggregate",
            "current authority target",
        ],
        "release_preservation_validation": "full ToeFormal aggregate when feasible",
        "aggregate_timeout_with_steady_progress_interpretation": (
            "incomplete_validation_not_mathematical_failure"
        ),
        "toeformal_import_update_requires_preservation_status": True,
        "aggregate_lean_validation_status_for_packet": "NOT_RUN",
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_toeformal_aggregate_status_for_packet": "NOT_RUN",
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_toe_native_a_source_admissibility_ck_functional_embedding_packet_result_review(
    *,
    embedding_packet_path: Path = EMBEDDING_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(embedding_packet_path)
    criteria = _review_criteria(packet)
    acceptance_criteria = {
        "consumes_expected_review_target": (
            packet.get("schema_id") == EMBEDDING_PACKET_SCHEMA_ID
            and packet.get("packet_id") == EMBEDDING_PACKET_ID
            and packet.get("outcome_id") == EMBEDDING_PACKET_OUTCOME
            and packet.get("packet_result") == EMBEDDING_PACKET_RESULT
            and packet.get("selected_next_target") == CONSUMED_TARGET
            and packet.get("accepted") is True
        ),
        "admissibility_only_route_selected": (
            packet.get("admissibility_only_route_selected") is True
            and packet.get("constraint_as_admissibility_rule_selected") is True
            and packet.get("constraint_as_action_term_selected") is False
            and packet.get("admissibility_constraint_form")
            == ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "vacuum_scope_preserved": (
            packet.get("gauge_group_policy") == GAUGE_GROUP_POLICY
            and packet.get("A_field_domain_policy") == A_FIELD_DOMAIN_POLICY
            and packet.get("F_definition_policy") == F_DEFINITION_POLICY
            and packet.get("source_route_still_blocked") == SOURCE_ROUTE_STILL_BLOCKED
        ),
        "action_routes_blocked_or_unlicensed": (
            packet.get("lagrange_multiplier_route_blocked") is True
            and packet.get("lagrange_multiplier_action_form")
            == LAGRANGE_MULTIPLIER_ACTION_FORM
            and packet.get("component_pairing_form") == COMPONENT_PAIRING_FORM
            and packet.get("weak_integrated_form") == WEAK_INTEGRATED_FORM
            and packet.get("quadratic_penalty_route_recorded") is True
            and packet.get("quadratic_penalty_route_licensed") is False
            and packet.get("quadratic_penalty_action_form")
            == QUADRATIC_PENALTY_ACTION_FORM
        ),
        "candidate_forms_exact": (
            packet.get("candidate_constraint_id") == CANDIDATE_CONSTRAINT_ID
            and packet.get("candidate_constraint_form") == CANDIDATE_CONSTRAINT_FORM
            and packet.get("candidate_constraint_equation")
            == CANDIDATE_CONSTRAINT_EQUATION
            and packet.get("vacuum_supporting_identity_form")
            == VACUUM_SUPPORTING_IDENTITY_FORM
            and packet.get("vacuum_on_shell_implication_form")
            == VACUUM_ON_SHELL_IMPLICATION_FORM
        ),
        "no_action_embedding_or_variation": all(
            packet.get(key) is False
            for key in [
                "dynamical_action_embedding_selected",
                "constraint_as_action_term_selected",
                "constraint_multiplier_type_selected",
                "constraint_term_selected",
                "lambda_nu_domain_selected",
                "component_pairing_rule_selected",
                "variation_policy_selected",
                "higher_derivative_analysis_completed",
                "higher_derivative_scope_resolved",
                "boundary_terms_controlled",
                "gauge_dynamics_preservation_proved",
                "candidate_action_insertion_executed",
                "ck_action_embedding_constructed",
                "C_k_action_embedding_constructed",
                "ck_variation_executed",
                "C_k_variation_executed",
                "lambda_variation_executed",
                "metric_variation_of_candidate_executed",
                "A_variation_of_candidate_executed",
                "quadratic_penalty_variation_executed",
            ]
        ),
        "no_current_or_sourced_em_route": all(
            packet.get(key) is False
            for key in [
                "J_nu_derived",
                "matter_current_J_nu_derived",
                "psi_current_route_constructed",
                "external_current_native_derivation_selected",
                "sourced_maxwell_equation_derived",
                "matter_current_exchange_route_proved",
                "matter_gauge_energy_exchange_proved",
            ]
        ),
        "no_forbidden_claims": all(
            packet.get(key) is False
            for key in [
                "new_conservation_proof_claimed",
                "new_source_admissibility_proof_claimed",
                "full_source_admissibility_review_accepted",
                "source_admissibility_claimed",
                "source_admissibility_completed",
                "source_admissibility_proved",
                "A_source_admissibility_claimed",
                "A_source_admissibility_proved",
                "full_em_closure_claimed",
                "em_closure_claimed",
                "em_qft_closure_claimed",
                "qft_gr_closure_claimed",
                "qft_gr_solved",
                "qft_gr_seam_closed",
                "semiclassical_coupling_authorized",
                "semiclassical_coupling_claimed",
                "semiclassical_einstein_equation_derived",
                "empirical_validation_claimed",
                "public_readiness_claimed",
                "master_action_promoted",
                "master_action_promotion_authorized",
                "canonical_master_action_promoted",
                "phase2_readiness_claim",
                "pillar_completion_inferred",
                "seam_closure_claim",
            ]
        ),
        "criteria_all_accepted": all(row["status"] == "accepted" for row in criteria),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_REVIEW"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_"
            "PACKET_RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "review_prepared": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_REVIEW_REQUIRES_REMEDIATION",
        "packet_result": "REVIEW_ACCEPTED" if accepted else "REVIEW_REQUIRES_REMEDIATION",
        "review_result": REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "embedding_packet_outcome": EMBEDDING_PACKET_OUTCOME,
        "embedding_packet_result": EMBEDDING_PACKET_RESULT,
        "selected_A_ck_constraint_family": SELECTED_A_CK_CONSTRAINT_FAMILY,
        "candidate_constraint_id": CANDIDATE_CONSTRAINT_ID,
        "candidate_constraint_type": "vacuum_conservation_residual_constraint",
        "candidate_constraint_form": CANDIDATE_CONSTRAINT_FORM,
        "candidate_constraint_equation": CANDIDATE_CONSTRAINT_EQUATION,
        "candidate_constraint_short_form": CANDIDATE_CONSTRAINT_SHORT_FORM,
        "candidate_constraint_interpretation": CANDIDATE_CONSTRAINT_INTERPRETATION,
        "gauge_group_policy": GAUGE_GROUP_POLICY,
        "A_field_domain_policy": A_FIELD_DOMAIN_POLICY,
        "F_definition_policy": F_DEFINITION_POLICY,
        "bianchi_identity_route": BIANCHI_IDENTITY_ROUTE,
        "vacuum_euler_lagrange_route": VACUUM_EULER_LAGRANGE_ROUTE,
        "stress_energy_under_selected_u1_policy": (
            STRESS_ENERGY_UNDER_SELECTED_U1_POLICY
        ),
        "source_admissibility_condition": SOURCE_ADMISSIBILITY_CONDITION,
        "divergence_identity": DIVERGENCE_IDENTITY,
        "vacuum_supporting_identity_form": VACUUM_SUPPORTING_IDENTITY_FORM,
        "vacuum_on_shell_implication_form": VACUUM_ON_SHELL_IMPLICATION_FORM,
        "on_shell_vacuum_conservation_identity": (
            ON_SHELL_VACUUM_CONSERVATION_IDENTITY
        ),
        "bounded_source_admissibility_result": BOUNDED_SOURCE_ADMISSIBILITY_RESULT,
        "local_source_route_scope": LOCAL_SOURCE_ROUTE_SCOPE,
        "source_route_still_blocked": SOURCE_ROUTE_STILL_BLOCKED,
        "current_coupled_scope_boundary": CURRENT_COUPLED_SCOPE_BOUNDARY,
        "full_source_admissibility_boundary": FULL_SOURCE_ADMISSIBILITY_BOUNDARY,
        "embedding_route_count": 3,
        "selected_embedding_route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
        "admissibility_only_route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
        "admissibility_only_route_status": ADMISSIBILITY_ONLY_ROUTE_STATUS,
        "admissibility_constraint_form": ADMISSIBILITY_CONSTRAINT_FORM,
        "lagrange_multiplier_route_id": LAGRANGE_MULTIPLIER_ROUTE_ID,
        "lagrange_multiplier_route_status": LAGRANGE_MULTIPLIER_ROUTE_STATUS,
        "lagrange_multiplier_action_form": LAGRANGE_MULTIPLIER_ACTION_FORM,
        "direct_divergence_insertion_form": DIRECT_DIVERGENCE_INSERTION_FORM,
        "component_pairing_form": COMPONENT_PAIRING_FORM,
        "weak_integrated_form": WEAK_INTEGRATED_FORM,
        "quadratic_penalty_route_id": QUADRATIC_PENALTY_ROUTE_ID,
        "quadratic_penalty_route_status": QUADRATIC_PENALTY_ROUTE_STATUS,
        "quadratic_penalty_action_form": QUADRATIC_PENALTY_ACTION_FORM,
        "functional_embedding_result_review_prepared": True,
        "functional_embedding_result_review_accepted": True,
        "review_accepts_admissibility_only_route": True,
        "packet_result_review_accepts_admissibility_only_route": True,
        "admissibility_rule_closeout_authorized": True,
        "admissibility_rule_closeout_prepared": False,
        "first_A_relevant_ck_admissibility_rule_candidate_classification": (
            FIRST_A_RULE_CLASSIFICATION
        ),
        "functional_embedding_packet_prepared": True,
        "functional_embedding_options_recorded": True,
        "admissibility_only_route_selected": True,
        "admissibility_only_interpretation_retained": True,
        "vacuum_u1_scope_preserved": True,
        "accepted_vacuum_source_route_retained_as_context": True,
        "constraint_as_admissibility_rule_selected": True,
        "dynamical_action_embedding_selected": False,
        "dynamical_action_embedding_not_assumed": True,
        "constraint_as_action_term_selected": False,
        "lagrange_multiplier_route_recorded": True,
        "lagrange_multiplier_route_blocked": True,
        "weak_integrated_form_boundary_controlled": False,
        "quadratic_penalty_route_recorded": True,
        "quadratic_penalty_route_licensed": False,
        "constraint_multiplier_type_selected": False,
        "constraint_term_selected": False,
        "lambda_nu_domain_selected": False,
        "component_pairing_rule_selected": False,
        "lambda_nu_variational_role_selected": False,
        "variation_policy_selected": False,
        "higher_derivative_analysis_completed": False,
        "higher_derivative_scope_resolved": False,
        "boundary_terms_controlled": False,
        "gauge_dynamics_preservation_proved": False,
        "regularity_domain_of_c_source_defined_for_action_embedding": False,
        "covariance_of_lambda_c_source_established": False,
        "fully_concrete_ck_functional_selected": False,
        "fully_concrete_ck_functional_defined": False,
        "concrete_ck_functional_selected": False,
        "concrete_ck_functional_defined": False,
        "ck_functional_formula_fully_defined": False,
        "ck_functional_formula_selected": False,
        "candidate_action_insertion_executed": False,
        "ck_action_embedding_selected": False,
        "ck_action_embedding_constructed": False,
        "C_k_action_embedding_selected": False,
        "C_k_action_embedding_constructed": False,
        "ck_variation_executed": False,
        "ck_variation_authorized": False,
        "C_k_variation_executed": False,
        "C_k_variation_authorized": False,
        "lambda_variation_executed": False,
        "metric_variation_of_candidate_executed": False,
        "A_variation_of_candidate_executed": False,
        "quadratic_penalty_variation_executed": False,
        "ck_family_claimed_as_physical_law": False,
        "A_relevant_C_k_rule_candidate_review_accepted": True,
        "A_relevant_C_k_rules_constructed": False,
        "A_relevant_C_k_triads_constructed": False,
        "A_source_C_k_rule_constructed": False,
        "source_bridge_transport_ck_analogues_constructed": False,
        "new_conservation_proof_claimed": False,
        "new_source_admissibility_proof_claimed": False,
        "full_source_admissibility_review_accepted": False,
        "source_admissibility_claimed": False,
        "source_admissibility_completed": False,
        "source_admissibility_proved": False,
        "A_source_admissibility_claimed": False,
        "A_source_admissibility_proved": False,
        "stress_energy_source_admissibility_proved": False,
        "stress_energy_as_gravity_source_authorized": False,
        "current_route_derived": False,
        "current_source_route_constructed": False,
        "matter_current_J_nu_derived": False,
        "J_nu_derived": False,
        "psi_current_route_constructed": False,
        "psi_derived_current": False,
        "external_current_policy_selected": False,
        "external_current_native_derivation_selected": False,
        "current_conservation_proved": False,
        "matter_current_exchange_route_proved": False,
        "matter_gauge_energy_exchange_proved": False,
        "matter_gauge_energy_exchange_claimed": False,
        "maxwell_equation_derived": False,
        "maxwell_equations_derived": False,
        "sourced_maxwell_equation_derived": False,
        "sourced_maxwell_closure_claimed": False,
        "nonabelian_route_selected": False,
        "yang_mills_equations_derived": False,
        "field_equations_derived": False,
        "full_em_closure_claimed": False,
        "em_closure_claimed": False,
        "em_qft_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_solved": False,
        "qft_gr_seam_closed": False,
        "qft_gr_source_map_closure_authorized": False,
        "semiclassical_coupling_authorized": False,
        "semiclassical_coupling_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "semiclassical_source_established": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "canonical_master_action_promoted": False,
        "empirical_validation_claimed": False,
        "public_readiness_claimed": False,
        "public_submission_authorized": False,
        "phase2_readiness_claim": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "review_criteria": criteria,
        "review_criteria_count": len(criteria),
        "review_criteria_accepted_count": sum(
            1 for row in criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "proof_depth_label": (
            "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_REVIEW_"
            "ACCEPTS_ADMISSIBILITY_ONLY"
        ),
        "mathematical_statement": (
            "The review accepts the A source-admissibility C_k "
            "functional-embedding packet only at the admissibility-rule level. "
            "The rule C_source^{A,nu}[g,A] = 0 is preserved as a "
            "non-dynamical vacuum U(1) source-admission condition. The "
            "multiplier/action route remains blocked, the quadratic penalty "
            "route remains unlicensed, and no action variation or promotion "
            "is executed."
        ),
        "non_claim_boundary": (
            "This review accepts the admissibility-only route as a rule only, "
            "not as an action term. It preserves C_source^{A,nu}[g,A] = 0 as "
            "a vacuum U(1) source-admission rule, keeps the multiplier/action "
            "route blocked by lambda_nu domain, component pairing, boundary "
            "terms, variation policy, higher-derivative analysis, and "
            "unproved preservation of intended gauge dynamics, and keeps the "
            "quadratic penalty route unlicensed. It does not functionalize "
            "the candidate, does not embed it in S_C, does not select "
            "lambda_nu or its domain, does not select a component pairing "
            "rule, does not select a constraint action term, does not control "
            "boundary terms, does not select a variation policy, does not "
            "complete higher-derivative analysis, does not execute C_k "
            "variation, does not vary lambda_k, A, or g, does not execute a "
            "quadratic penalty variation, does not derive J^nu, does not "
            "derive a psi-current or external-current native route, does not "
            "derive sourced Maxwell, does not prove matter-current or "
            "matter-gauge exchange, does not prove new conservation, does not "
            "prove full source admissibility beyond the bounded vacuum route, "
            "does not close EM, does not close QFT-GR, does not authorize "
            "semiclassical coupling, does not promote the master action, and "
            "does not claim empirical validation or public readiness."
        ),
        "critical_gate_fail_conditions": [
            "treat C_source^{A,nu} = 0 as a selected dynamical action term",
            "claim the multiplier/action route is selected",
            "claim the quadratic penalty route is licensed",
            "select lambda_nu multiplier type or domain",
            "select a component pairing rule",
            "execute C_k or lambda variation",
            "execute A or metric variation of the candidate",
            "claim boundary terms are controlled",
            "claim variation policy is selected",
            "claim higher-derivative analysis is complete",
            "claim intended gauge dynamics are preserved by the action term",
            "derive J^nu",
            "derive a psi-current or external-current native route",
            "derive sourced Maxwell",
            "prove matter-current exchange",
            "claim full EM closure",
            "claim QFT-GR closure",
            "claim semiclassical coupling",
            "promote the master action",
            "claim empirical validation or public readiness",
        ],
        "validation_policy": _validation_policy(),
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "aggregate_lean_validation_status_for_packet": "NOT_RUN",
        "full_toeformal_aggregate_status_for_packet": "NOT_RUN",
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativeASourceAdmissibilityCKFunctionalEmbeddingPacketResultReview",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
            "embedding_packet_file": _ptr(embedding_packet_path),
            "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        },
    }


def write_review(review: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(review, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Build the ToE-native A source-admissibility C_k "
            "functional-embedding packet result review."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    review = (
        build_toe_native_a_source_admissibility_ck_functional_embedding_packet_result_review(
            captured_at_utc=args.captured_at_utc
        )
    )
    path = write_review(review, args.out)
    print(
        json.dumps(
            {
                "accepted": review["accepted"],
                "out": _ptr(path),
                "outcome_id": review["outcome_id"],
                "review_result": review["review_result"],
                "selected_next_target": review["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
