from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_a_source_admissibility_ck_constraint_candidate_packet_result_review_report import (
    A_FIELD_DOMAIN_POLICY,
    BIANCHI_IDENTITY_ROUTE,
    BOUNDED_SOURCE_ADMISSIBILITY_RESULT,
    CANDIDATE_ACTION_INSERTION_FORM,
    CANDIDATE_CONSTRAINT_EQUATION,
    CANDIDATE_CONSTRAINT_FORM,
    CANDIDATE_CONSTRAINT_ID,
    CANDIDATE_CONSTRAINT_INTERPRETATION,
    CANDIDATE_CONSTRAINT_SHORT_FORM,
    CURRENT_COUPLED_SCOPE_BOUNDARY,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as CANDIDATE_REVIEW_PATH,
    DIVERGENCE_IDENTITY,
    F_DEFINITION_POLICY,
    FULL_SOURCE_ADMISSIBILITY_BOUNDARY,
    GAUGE_GROUP_POLICY,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    LOCAL_SOURCE_ROUTE_SCOPE,
    NEXT_TARGET as CONSUMED_TARGET,
    ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
    OUTCOME_ID as CANDIDATE_REVIEW_OUTCOME,
    PACKET_ID as CANDIDATE_REVIEW_PACKET_ID,
    PACKET_CLASSIFICATION as CANDIDATE_REVIEW_CLASSIFICATION,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    REVIEW_RESULT as CANDIDATE_REVIEW_RESULT,
    SCHEMA_ID as CANDIDATE_REVIEW_SCHEMA_ID,
    SELECTED_A_CK_CONSTRAINT_FAMILY,
    SOURCE_ADMISSIBILITY_CONDITION,
    SOURCE_ROUTE_STILL_BLOCKED,
    STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
    VACUUM_EULER_LAGRANGE_ROUTE,
    VACUUM_ON_SHELL_IMPLICATION_FORM,
    VACUUM_SUPPORTING_IDENTITY_FORM,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-22T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_"
    "20260622_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_v0"
)
PACKET_RESULT = (
    "OPTIONS_RECORDED_ADMISSIBILITY_ONLY_ROUTE_SELECTED_NO_ACTION_VARIATION"
)
OUTCOME_ID = (
    "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_"
    "PREPARED_"
    + PACKET_RESULT
)
PACKET_CLASSIFICATION = (
    "toe_native_A_source_admissibility_ck_functional_embedding_packet_records_"
    "options_and_selects_admissibility_only_no_action_variation"
)
NEXT_TARGET = (
    "review_toe_native_A_source_admissibility_ck_functional_embedding_packet_result"
)
NEXT_TARGET_KIND = (
    "toe_native_A_source_admissibility_ck_functional_embedding_packet_result_review"
)

ADMISSIBILITY_ONLY_ROUTE_ID = "A_source_ck_admissibility_only_route"
ADMISSIBILITY_CONSTRAINT_FORM = CANDIDATE_CONSTRAINT_EQUATION
ADMISSIBILITY_ONLY_ROUTE_STATUS = "selected_non_dynamical_admissibility_rule"
LAGRANGE_MULTIPLIER_ROUTE_ID = "A_source_ck_lagrange_multiplier_action_route"
LAGRANGE_MULTIPLIER_ACTION_FORM = (
    "S_C^A = integral_M dVol_g lambda_nu C_source^{A,nu}"
)
DIRECT_DIVERGENCE_INSERTION_FORM = (
    "S_C^A = integral_M dVol_g lambda_nu nabla_mu T_A^{mu nu}"
)
COMPONENT_PAIRING_FORM = "lambda_nu C_source^{A,nu}"
WEAK_INTEGRATED_FORM = (
    "integral_M dVol_g lambda_nu nabla_mu T_A^{mu nu} = - integral_M "
    "dVol_g (nabla_mu lambda_nu) T_A^{mu nu} + boundary"
)
LAGRANGE_MULTIPLIER_ROUTE_STATUS = (
    "blocked_by_multiplier_domain_pairing_boundary_variation_and_dynamics_scope"
)
QUADRATIC_PENALTY_ROUTE_ID = "A_source_ck_quadratic_penalty_route"
QUADRATIC_PENALTY_ACTION_FORM = (
    "S_C^A = integral_M dVol_g C_source^A_nu C_source^{A,nu}"
)
QUADRATIC_PENALTY_ROUTE_STATUS = "recorded_unlicensed_dynamical_penalty"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_"
    "20260622_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeASourceAdmissibilityCKFunctionalEmbeddingPacket.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _embedding_routes() -> list[dict[str, Any]]:
    return [
        {
            "route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
            "route_type": "admissibility_only_rule",
            "status": ADMISSIBILITY_ONLY_ROUTE_STATUS,
            "constraint_form": ADMISSIBILITY_CONSTRAINT_FORM,
            "plain_meaning": (
                "The vacuum U(1) gauge stress-energy route is admitted only "
                "if its conservation residual vanishes."
            ),
            "action_term_selected": False,
            "action_variation_executed": False,
            "selected_for_current_packet": True,
        },
        {
            "route_id": LAGRANGE_MULTIPLIER_ROUTE_ID,
            "route_type": "lagrange_multiplier_action_embedding",
            "status": LAGRANGE_MULTIPLIER_ROUTE_STATUS,
            "action_form": LAGRANGE_MULTIPLIER_ACTION_FORM,
            "direct_divergence_insertion_form": DIRECT_DIVERGENCE_INSERTION_FORM,
            "component_pairing_form": COMPONENT_PAIRING_FORM,
            "weak_integrated_form": WEAK_INTEGRATED_FORM,
            "blocking_reasons": [
                "lambda_nu domain not selected",
                "component pairing rule not selected",
                "boundary terms not controlled",
                "variation policy not selected",
                "higher-derivative analysis not completed",
                "no proof that the action term preserves intended gauge dynamics",
            ],
            "action_term_selected": False,
            "action_variation_executed": False,
            "selected_for_current_packet": False,
        },
        {
            "route_id": QUADRATIC_PENALTY_ROUTE_ID,
            "route_type": "quadratic_penalty_action_embedding",
            "status": QUADRATIC_PENALTY_ROUTE_STATUS,
            "action_form": QUADRATIC_PENALTY_ACTION_FORM,
            "blocking_reasons": [
                "would turn a source-admissibility rule into a new dynamical penalty term",
                "would require metric, regularity, and derivative-order control",
                "would require a proof that gauge dynamics are not unintentionally changed",
            ],
            "action_term_selected": False,
            "action_variation_executed": False,
            "selected_for_current_packet": False,
        },
    ]


def _review_rows(candidate_review: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "consumes_expected_functional_embedding_target",
            "status": "accepted",
            "evidence": candidate_review.get("selected_next_target"),
            "assessment": "The candidate review authorized this functional-embedding packet.",
        },
        {
            "row_id": "vacuum_conservation_residual_candidate_carried_forward",
            "status": "accepted",
            "evidence": [
                CANDIDATE_CONSTRAINT_FORM,
                CANDIDATE_CONSTRAINT_EQUATION,
            ],
            "assessment": "The A source conservation residual candidate is carried forward exactly.",
        },
        {
            "row_id": "vacuum_u1_route_context_carried_forward",
            "status": "accepted",
            "evidence": [
                GAUGE_GROUP_POLICY,
                A_FIELD_DOMAIN_POLICY,
                F_DEFINITION_POLICY,
                VACUUM_EULER_LAGRANGE_ROUTE,
                STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
                BOUNDED_SOURCE_ADMISSIBILITY_RESULT,
            ],
            "assessment": "The local classical vacuum U(1) on-shell route remains the only accepted context.",
        },
        {
            "row_id": "three_embedding_routes_recorded",
            "status": "accepted",
            "evidence": [
                ADMISSIBILITY_ONLY_ROUTE_ID,
                LAGRANGE_MULTIPLIER_ROUTE_ID,
                QUADRATIC_PENALTY_ROUTE_ID,
            ],
            "assessment": "Admissibility-only, multiplier-action, and penalty routes are recorded.",
        },
        {
            "row_id": "admissibility_only_route_selected",
            "status": "accepted",
            "evidence": ADMISSIBILITY_CONSTRAINT_FORM,
            "assessment": "The packet selects only the non-dynamical admissibility rule.",
        },
        {
            "row_id": "lagrange_multiplier_route_blocked",
            "status": "accepted",
            "evidence": [
                LAGRANGE_MULTIPLIER_ACTION_FORM,
                COMPONENT_PAIRING_FORM,
                WEAK_INTEGRATED_FORM,
            ],
            "assessment": (
                "The multiplier route is blocked by missing lambda domain, "
                "pairing, boundary, variation, higher-derivative, and "
                "gauge-dynamics preservation checks."
            ),
        },
        {
            "row_id": "quadratic_penalty_route_unlicensed",
            "status": "accepted",
            "evidence": QUADRATIC_PENALTY_ACTION_FORM,
            "assessment": "The penalty route is recorded but unlicensed because it would change dynamics.",
        },
        {
            "row_id": "no_action_embedding_or_variation_executed",
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
            "assessment": "No action embedding or variation is executed.",
        },
        {
            "row_id": "no_current_or_sourced_em_route",
            "status": "accepted",
            "evidence": [
                "J_nu_derived=false",
                "psi_current_route_constructed=false",
                "external_current_native_derivation_selected=false",
                "sourced_maxwell_equation_derived=false",
                "matter_current_exchange_route_proved=false",
            ],
            "assessment": "No current, sourced Maxwell, or matter/current exchange route is introduced.",
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
            "assessment": "Closure, coupling, empirical validation, and promotion remain blocked.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "toe_native_A_source_admissibility_ck_functional_embedding_packet"
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


def build_toe_native_a_source_admissibility_ck_functional_embedding_packet(
    *,
    candidate_review_path: Path = CANDIDATE_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    candidate_review = _read_json(candidate_review_path)
    routes = _embedding_routes()
    review_rows = _review_rows(candidate_review)
    acceptance_criteria = {
        "consumes_expected_target": (
            candidate_review.get("schema_id") == CANDIDATE_REVIEW_SCHEMA_ID
            and candidate_review.get("packet_id") == CANDIDATE_REVIEW_PACKET_ID
            and candidate_review.get("outcome_id") == CANDIDATE_REVIEW_OUTCOME
            and candidate_review.get("review_result") == CANDIDATE_REVIEW_RESULT
            and candidate_review.get("selected_next_target") == CONSUMED_TARGET
            and candidate_review.get("accepted") is True
        ),
        "candidate_forms_carried_forward": (
            candidate_review.get("candidate_constraint_id") == CANDIDATE_CONSTRAINT_ID
            and candidate_review.get("candidate_constraint_form")
            == CANDIDATE_CONSTRAINT_FORM
            and candidate_review.get("candidate_constraint_equation")
            == CANDIDATE_CONSTRAINT_EQUATION
        ),
        "vacuum_u1_scope_carried_forward": (
            candidate_review.get("gauge_group_policy") == GAUGE_GROUP_POLICY
            and candidate_review.get("A_field_domain_policy") == A_FIELD_DOMAIN_POLICY
            and candidate_review.get("F_definition_policy") == F_DEFINITION_POLICY
            and candidate_review.get("vacuum_euler_lagrange_route")
            == VACUUM_EULER_LAGRANGE_ROUTE
            and candidate_review.get("source_route_still_blocked")
            == SOURCE_ROUTE_STILL_BLOCKED
        ),
        "three_routes_recorded": len(routes) == 3,
        "admissibility_only_selected": (
            routes[0]["route_id"] == ADMISSIBILITY_ONLY_ROUTE_ID
            and routes[0]["selected_for_current_packet"] is True
            and routes[0]["action_term_selected"] is False
        ),
        "action_routes_not_licensed": all(
            route["action_term_selected"] is False
            and route["action_variation_executed"] is False
            for route in routes
        ),
        "multiplier_route_blocked": (
            routes[1]["status"] == LAGRANGE_MULTIPLIER_ROUTE_STATUS
            and "lambda_nu domain not selected" in routes[1]["blocking_reasons"]
            and "component pairing rule not selected" in routes[1]["blocking_reasons"]
            and "boundary terms not controlled" in routes[1]["blocking_reasons"]
            and "variation policy not selected" in routes[1]["blocking_reasons"]
            and "higher-derivative analysis not completed"
            in routes[1]["blocking_reasons"]
        ),
        "penalty_route_unlicensed": (
            routes[2]["status"] == QUADRATIC_PENALTY_ROUTE_STATUS
            and "new dynamical penalty term" in routes[2]["blocking_reasons"][0]
        ),
        "review_rows_all_accepted": all(
            row["status"] == "accepted" for row in review_rows
        ),
        "next_review_target_selected": (
            NEXT_TARGET
            == "review_toe_native_A_source_admissibility_ck_functional_embedding_packet_result"
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_REQUIRES_REMEDIATION",
        "packet_result": PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "candidate_review_outcome": CANDIDATE_REVIEW_OUTCOME,
        "candidate_review_result": CANDIDATE_REVIEW_RESULT,
        "candidate_review_classification": CANDIDATE_REVIEW_CLASSIFICATION,
        "selected_A_ck_constraint_family": SELECTED_A_CK_CONSTRAINT_FAMILY,
        "candidate_constraint_id": CANDIDATE_CONSTRAINT_ID,
        "candidate_constraint_type": "vacuum_conservation_residual_constraint",
        "candidate_constraint_form": CANDIDATE_CONSTRAINT_FORM,
        "candidate_constraint_equation": CANDIDATE_CONSTRAINT_EQUATION,
        "candidate_constraint_short_form": CANDIDATE_CONSTRAINT_SHORT_FORM,
        "candidate_constraint_interpretation": CANDIDATE_CONSTRAINT_INTERPRETATION,
        "candidate_action_insertion_form": CANDIDATE_ACTION_INSERTION_FORM,
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
        "embedding_routes": routes,
        "embedding_route_count": len(routes),
        "selected_embedding_route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
        "admissibility_only_route_selected": True,
        "admissibility_constraint_form": ADMISSIBILITY_CONSTRAINT_FORM,
        "lagrange_multiplier_route_recorded": True,
        "lagrange_multiplier_route_blocked": True,
        "lagrange_multiplier_action_form": LAGRANGE_MULTIPLIER_ACTION_FORM,
        "direct_divergence_insertion_form": DIRECT_DIVERGENCE_INSERTION_FORM,
        "component_pairing_form": COMPONENT_PAIRING_FORM,
        "weak_integrated_form": WEAK_INTEGRATED_FORM,
        "weak_integrated_form_boundary_controlled": False,
        "quadratic_penalty_route_recorded": True,
        "quadratic_penalty_route_licensed": False,
        "quadratic_penalty_action_form": QUADRATIC_PENALTY_ACTION_FORM,
        "functional_embedding_packet_prepared": True,
        "functional_embedding_options_recorded": True,
        "admissibility_only_interpretation_retained": True,
        "vacuum_u1_scope_preserved": True,
        "accepted_vacuum_source_route_retained_as_context": True,
        "dynamical_action_embedding_selected": False,
        "dynamical_action_embedding_not_assumed": True,
        "constraint_as_admissibility_rule_selected": True,
        "constraint_as_action_term_selected": False,
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
        "review_rows": review_rows,
        "review_row_count": len(review_rows),
        "review_row_accepted_count": sum(
            1 for row in review_rows if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "proof_depth_label": (
            "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_OPTIONS_"
            "RECORDED_ADMISSIBILITY_ONLY"
        ),
        "mathematical_statement": (
            "The functional-embedding packet records three routes for the "
            "ToE-native A source-admissibility C_k candidate. The "
            "admissibility-only route C_source^{A,nu}[g,A] = 0 is selected "
            "as a non-dynamical vacuum U(1) source-admission rule. The "
            "multiplier route S_C^A = integral_M dVol_g lambda_nu "
            "C_source^{A,nu} is blocked by unselected lambda domain, "
            "component pairing, boundary terms, variation policy, higher-"
            "derivative analysis, and the missing proof that it preserves "
            "intended gauge dynamics. The quadratic penalty route is "
            "recorded but unlicensed because it would create a new "
            "dynamical penalty term. No action variation is executed."
        ),
        "non_claim_boundary": (
            "This packet records functional-embedding options for the A "
            "source-admissibility conservation residual and selects the "
            "admissibility-only route. It does not functionalize the "
            "candidate, does not embed it in S_C, does not select lambda_nu "
            "or its domain, does not select a component pairing rule, does "
            "not select a constraint action term, does not control boundary "
            "terms, does not select a variation policy, does not complete "
            "higher-derivative analysis, does not prove preservation of the "
            "intended gauge dynamics, does not license the quadratic penalty "
            "route, does not execute C_k variation, does not vary lambda_k, "
            "A, or g, does not derive J^nu, does not derive a psi-current or "
            "external-current native route, does not derive sourced Maxwell, "
            "does not prove matter-current or matter-gauge exchange, does "
            "not accept full source admissibility beyond the bounded vacuum "
            "route, does not close EM, does not close QFT-GR, does not "
            "authorize semiclassical coupling, does not promote the master "
            "action, and does not claim empirical validation or public "
            "readiness. The result remains a vacuum U(1), admissibility-only "
            "rule; no C_k action embedding, no C_k variation, and no "
            "master-action promotion follow."
        ),
        "critical_gate_fail_conditions": [
            "claim the multiplier route is selected as an action term",
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
            "ToeFormal.Derivation.ToeNativeASourceAdmissibilityCKFunctionalEmbeddingPacket",
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
            "candidate_review_file": _ptr(candidate_review_path),
            "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        },
    }


def write_packet(packet: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(packet, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Build the ToE-native A source-admissibility C_k functional "
            "embedding packet."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    packet = build_toe_native_a_source_admissibility_ck_functional_embedding_packet(
        captured_at_utc=args.captured_at_utc
    )
    path = write_packet(packet, args.out)
    print(
        json.dumps(
            {
                "accepted": packet["accepted"],
                "out": _ptr(path),
                "outcome_id": packet["outcome_id"],
                "packet_result": packet["packet_result"],
                "selected_embedding_route_id": packet["selected_embedding_route_id"],
                "selected_next_target": packet["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
