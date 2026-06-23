from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_a_bridge_admissibility_ck_constraint_candidate_packet_result_review_report import (
    A_BRIDGE_CANDIDATE_ID,
    A_BRIDGE_CANDIDATE_TYPE,
    A_BRIDGE_CONSTRAINT_EQUATION,
    A_BRIDGE_CONSTRAINT_FORM,
    A_BRIDGE_FIELD_EQUATION_MATCH,
    A_BRIDGE_RULE_PLAIN_MEANING,
    A_BRIDGE_ROUTE_ALIGNMENT_SEQUENCE,
    A_BRIDGE_SOURCE_RESIDUAL_MATCH,
    A_BRIDGE_STRESS_ENERGY_MATCH,
    A_FIELD_DOMAIN_POLICY,
    BIANCHI_IDENTITY_ROUTE,
    BOUNDED_SOURCE_ADMISSIBILITY_RESULT,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as CANDIDATE_REVIEW_PATH,
    DIVERGENCE_IDENTITY,
    F_DEFINITION_POLICY,
    FULL_TOEFORMAL_STATUS,
    GAUGE_GROUP_POLICY,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    LOCAL_SOURCE_ROUTE_SCOPE,
    NEXT_TARGET as CONSUMED_TARGET,
    ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
    OUTCOME_ID as CANDIDATE_REVIEW_OUTCOME,
    PACKET_ID as CANDIDATE_REVIEW_PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    REVIEW_RESULT as CANDIDATE_REVIEW_RESULT,
    SCHEMA_ID as CANDIDATE_REVIEW_SCHEMA_ID,
    SELECTED_A_CK_CONSTRAINT_FAMILY,
    SELECTED_A_CK_OPTION_CLASS,
    SOURCE_ADMISSIBILITY_CONDITION,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    SOURCE_ROUTE_STILL_BLOCKED,
    SOURCE_RULE_CLOSEOUT_OUTCOME,
    STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
    VACUUM_EULER_LAGRANGE_ROUTE,
    VACUUM_ON_SHELL_IMPLICATION_FORM,
    VACUUM_SUPPORTING_IDENTITY_FORM,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-22T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_"
    "20260622_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_v0"
PACKET_RESULT = "OPTIONS_RECORDED_ADMISSIBILITY_ONLY_ROUTE_SELECTED_NO_ACTION_VARIATION"
OUTCOME_ID = (
    "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_"
    "PREPARED_"
    + PACKET_RESULT
)
PACKET_CLASSIFICATION = (
    "toe_native_A_bridge_admissibility_ck_functional_embedding_packet_records_"
    "options_and_selects_admissibility_only_no_action_variation"
)
NEXT_TARGET = "review_toe_native_A_bridge_admissibility_ck_functional_embedding_packet_result"
NEXT_TARGET_KIND = "toe_native_A_bridge_admissibility_ck_functional_embedding_packet_result_review"

ADMISSIBILITY_ONLY_ROUTE_ID = "A_bridge_ck_admissibility_only_route"
BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM = "C_bridge^A = 0"
ADMISSIBILITY_ONLY_ROUTE_STATUS = "selected_non_dynamical_route_consistency_rule"
LAGRANGE_MULTIPLIER_ROUTE_ID = "A_bridge_ck_lagrange_multiplier_action_route"
LAGRANGE_MULTIPLIER_ACTION_FORM = (
    "S_C^A_bridge = integral_M dVol_g Lambda_bridge dot C_bridge^A"
)
LAGRANGE_MULTIPLIER_ROUTE_STATUS = (
    "blocked_by_component_pairing_multiplier_domain_covariance_boundary_"
    "variation_and_gauge_dynamics_scope"
)
PENALTY_ROUTE_ID = "A_bridge_ck_penalty_route"
PENALTY_ACTION_FORM = "S_C^A_bridge = integral_M dVol_g norm(C_bridge^A)^2"
PENALTY_ROUTE_STATUS = "recorded_unlicensed_dynamical_penalty"
COMPONENT_PAIRING_REQUIREMENTS = [
    "component pairing rule not selected",
    "multiplier domain not selected",
    "covariance control not established",
    "boundary-term policy not selected",
    "variation policy not selected",
    "no proof that the action term preserves intended gauge dynamics",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_"
    "20260622_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeABridgeAdmissibilityCKFunctionalEmbeddingPacket.lean"
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
            "route_type": "admissibility_only_route_consistency_rule",
            "status": ADMISSIBILITY_ONLY_ROUTE_STATUS,
            "constraint_form": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
            "plain_meaning": (
                "The vacuum U(1) A bridge route is admitted only if the "
                "master-action gauge route, vacuum U(1) field-equation route, "
                "gauge stress-energy route, and source-admissibility residual "
                "match under the selected policy."
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
            "blocking_reasons": COMPONENT_PAIRING_REQUIREMENTS,
            "action_term_selected": False,
            "action_variation_executed": False,
            "selected_for_current_packet": False,
        },
        {
            "route_id": PENALTY_ROUTE_ID,
            "route_type": "quadratic_or_norm_penalty_embedding",
            "status": PENALTY_ROUTE_STATUS,
            "action_form": PENALTY_ACTION_FORM,
            "blocking_reasons": [
                "no norm over the heterogeneous route tuple is defined",
                "would turn a bridge-admissibility rule into a new dynamical penalty term",
                "would require metric, regularity, covariance, and derivative-order control",
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
            "assessment": "The bridge candidate review authorized this packet.",
        },
        {
            "row_id": "bridge_tuple_carried_forward",
            "status": "accepted",
            "evidence": A_BRIDGE_CONSTRAINT_FORM,
            "assessment": "The route-consistency tuple is carried forward exactly.",
        },
        {
            "row_id": "bridge_condition_carried_forward",
            "status": "accepted",
            "evidence": A_BRIDGE_CONSTRAINT_EQUATION,
            "assessment": "The condition C_bridge^A = 0 is preserved.",
        },
        {
            "row_id": "bridge_components_carried_forward",
            "status": "accepted",
            "evidence": [
                A_BRIDGE_FIELD_EQUATION_MATCH,
                A_BRIDGE_STRESS_ENERGY_MATCH,
                A_BRIDGE_SOURCE_RESIDUAL_MATCH,
            ],
            "assessment": (
                "The E_A route match, T_A route match, and C_source^A "
                "residual match components are preserved."
            ),
        },
        {
            "row_id": "vacuum_u1_context_carried_forward",
            "status": "accepted",
            "evidence": [
                GAUGE_GROUP_POLICY,
                A_FIELD_DOMAIN_POLICY,
                F_DEFINITION_POLICY,
                VACUUM_EULER_LAGRANGE_ROUTE,
                LOCAL_SOURCE_ROUTE_SCOPE,
            ],
            "assessment": "The bounded local classical vacuum U(1) context is preserved.",
        },
        {
            "row_id": "three_embedding_routes_recorded",
            "status": "accepted",
            "evidence": [
                ADMISSIBILITY_ONLY_ROUTE_ID,
                LAGRANGE_MULTIPLIER_ROUTE_ID,
                PENALTY_ROUTE_ID,
            ],
            "assessment": "The admissibility-only, multiplier, and penalty routes are recorded.",
        },
        {
            "row_id": "admissibility_only_route_selected",
            "status": "accepted",
            "evidence": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
            "assessment": "Only the non-dynamical route-consistency rule is selected.",
        },
        {
            "row_id": "multiplier_action_route_blocked",
            "status": "accepted",
            "evidence": LAGRANGE_MULTIPLIER_ACTION_FORM,
            "assessment": (
                "The multiplier route is blocked by missing component pairing, "
                "multiplier domain, covariance control, boundary policy, "
                "variation policy, and gauge-dynamics preservation proof."
            ),
        },
        {
            "row_id": "penalty_route_unlicensed",
            "status": "accepted",
            "evidence": PENALTY_ACTION_FORM,
            "assessment": (
                "The penalty route is recorded but unlicensed because no norm "
                "over the heterogeneous route tuple is defined and it would "
                "become a new dynamical penalty term."
            ),
        },
        {
            "row_id": "no_action_embedding_or_variation_executed",
            "status": "accepted",
            "evidence": [
                "C_k_action_embedding_constructed=false",
                "C_k_variation_executed=false",
                "lambda_variation_executed=false",
                "A_variation_of_candidate_executed=false",
                "metric_variation_of_candidate_executed=false",
            ],
            "assessment": "No C_k action embedding or variation is executed.",
        },
        {
            "row_id": "no_current_sourced_maxwell_exchange_or_closure",
            "status": "accepted",
            "evidence": [
                "J_nu_derived=false",
                "psi_current_route_constructed=false",
                "external_current_native_derivation_selected=false",
                "sourced_maxwell_equation_derived=false",
                "matter_current_exchange_route_proved=false",
                "full_em_closure_claimed=false",
            ],
            "assessment": "No current, sourced Maxwell, matter/current exchange, or EM closure is introduced.",
        },
        {
            "row_id": "no_qft_gr_coupling_validation_or_promotion",
            "status": "accepted",
            "evidence": [
                "qft_gr_closure_claimed=false",
                "semiclassical_coupling_authorized=false",
                "empirical_validation_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": "QFT-GR closure, coupling, validation, and promotion remain blocked.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_A_bridge_admissibility_ck_functional_embedding_packet",
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
        "aggregate_lean_validation_status_for_packet": FULL_TOEFORMAL_STATUS,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def _false_boundary_flags() -> dict[str, bool]:
    return {
        "bridge_proof_claimed": False,
        "bridge_candidate_rule_proved": False,
        "A_bridge_candidate_rule_proved": False,
        "bridge_admissibility_claimed": False,
        "bridge_admissibility_proved": False,
        "A_bridge_admissibility_claimed": False,
        "A_bridge_admissibility_proved": False,
        "bridge_route_alignment_verified": False,
        "A_bridge_route_alignment_verified": False,
        "route_consistency_tuple_proved": False,
        "field_equation_match_proved": False,
        "stress_energy_match_proved": False,
        "source_residual_match_proved": False,
        "dynamical_action_embedding_selected": False,
        "constraint_as_action_term_selected": False,
        "bridge_candidate_recorded_as_action_term": False,
        "A_bridge_candidate_recorded_as_action_term": False,
        "bridge_candidate_recorded_as_new_dynamical_law": False,
        "A_bridge_candidate_recorded_as_new_dynamical_law": False,
        "constraint_multiplier_type_selected": False,
        "constraint_term_selected": False,
        "multiplier_type_selected": False,
        "multiplier_domain_selected": False,
        "component_pairing_rule_selected": False,
        "covariance_control_established": False,
        "covariance_of_multiplier_pairing_established": False,
        "boundary_term_policy_selected": False,
        "boundary_terms_controlled": False,
        "variation_policy_selected": False,
        "variation_policy_for_embedding_selected": False,
        "gauge_dynamics_preservation_proved": False,
        "heterogeneous_tuple_norm_defined": False,
        "penalty_route_licensed": False,
        "quadratic_penalty_route_licensed": False,
        "fully_concrete_ck_functional_selected": False,
        "fully_concrete_ck_functional_defined": False,
        "concrete_ck_functional_selected": False,
        "concrete_ck_functional_defined": False,
        "ck_functional_formula_fully_defined": False,
        "ck_functional_formula_selected": False,
        "ck_action_embedding_claimed": False,
        "ck_action_embedding_selected": False,
        "ck_action_embedding_constructed": False,
        "C_k_action_embedding_selected": False,
        "C_k_action_embedding_constructed": False,
        "candidate_action_insertion_executed": False,
        "ck_variation_executed": False,
        "ck_variation_authorized": False,
        "C_k_variation_executed": False,
        "C_k_variation_authorized": False,
        "lambda_variation_executed": False,
        "metric_variation_of_candidate_executed": False,
        "A_variation_of_candidate_executed": False,
        "penalty_variation_executed": False,
        "new_conservation_proof_claimed": False,
        "new_source_admissibility_proof_claimed": False,
        "source_admissibility_claimed": False,
        "source_admissibility_completed": False,
        "source_admissibility_proved": False,
        "A_source_admissibility_claimed": False,
        "A_source_admissibility_proved": False,
        "stress_energy_as_gravity_source_authorized": False,
        "stress_energy_source_admissibility_proved": False,
        "current_route_derived": False,
        "current_source_route_constructed": False,
        "matter_current_J_nu_derived": False,
        "J_nu_derived": False,
        "psi_current_route_constructed": False,
        "psi_derived_current": False,
        "external_current_policy_selected": False,
        "external_current_native_derivation_selected": False,
        "current_conservation_proved": False,
        "current_conservation_theorem_claimed": False,
        "matter_current_exchange_route_proved": False,
        "matter_gauge_energy_exchange_proved": False,
        "matter_gauge_energy_exchange_claimed": False,
        "maxwell_equation_derived": False,
        "maxwell_equations_derived": False,
        "sourced_maxwell_equation_derived": False,
        "sourced_maxwell_closure_claimed": False,
        "sourced_maxwell_route_derived": False,
        "matter_current_exchange_derived": False,
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
    }


def build_toe_native_a_bridge_admissibility_ck_functional_embedding_packet(
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
        "bridge_tuple_exact": (
            candidate_review.get("A_bridge_candidate_id") == A_BRIDGE_CANDIDATE_ID
            and candidate_review.get("A_bridge_candidate_type") == A_BRIDGE_CANDIDATE_TYPE
            and candidate_review.get("A_bridge_constraint_form")
            == A_BRIDGE_CONSTRAINT_FORM
            and candidate_review.get("A_bridge_constraint_equation")
            == A_BRIDGE_CONSTRAINT_EQUATION
        ),
        "bridge_components_exact": (
            candidate_review.get("A_bridge_field_equation_match")
            == A_BRIDGE_FIELD_EQUATION_MATCH
            and candidate_review.get("A_bridge_stress_energy_match")
            == A_BRIDGE_STRESS_ENERGY_MATCH
            and candidate_review.get("A_bridge_source_residual_match")
            == A_BRIDGE_SOURCE_RESIDUAL_MATCH
        ),
        "selected_family_exact": (
            candidate_review.get("selected_A_ck_option_class")
            == SELECTED_A_CK_OPTION_CLASS
            and candidate_review.get("selected_A_ck_constraint_family")
            == SELECTED_A_CK_CONSTRAINT_FAMILY
        ),
        "source_rule_context_exact": (
            candidate_review.get("source_rule_closeout_outcome")
            == SOURCE_RULE_CLOSEOUT_OUTCOME
            and candidate_review.get("source_candidate_constraint_id")
            == SOURCE_CANDIDATE_CONSTRAINT_ID
            and candidate_review.get("source_candidate_constraint_form")
            == SOURCE_CANDIDATE_CONSTRAINT_FORM
            and candidate_review.get("source_candidate_constraint_equation")
            == SOURCE_CANDIDATE_CONSTRAINT_EQUATION
            and candidate_review.get("source_admissibility_constraint_form")
            == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "vacuum_u1_context_exact": (
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
        "multiplier_route_blocked": (
            routes[1]["status"] == LAGRANGE_MULTIPLIER_ROUTE_STATUS
            and COMPONENT_PAIRING_REQUIREMENTS == routes[1]["blocking_reasons"]
        ),
        "penalty_route_unlicensed": (
            routes[2]["status"] == PENALTY_ROUTE_STATUS
            and "no norm over the heterogeneous route tuple is defined"
            in routes[2]["blocking_reasons"]
        ),
        "action_routes_not_licensed": all(
            route["action_term_selected"] is False
            and route["action_variation_executed"] is False
            for route in routes
        ),
        "review_rows_all_accepted": all(
            row["status"] == "accepted" for row in review_rows
        ),
        "next_review_target_selected": NEXT_TARGET
        == "review_toe_native_A_bridge_admissibility_ck_functional_embedding_packet_result",
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET"
    )
    route_sequence = " -> ".join(A_BRIDGE_ROUTE_ALIGNMENT_SEQUENCE)
    packet: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_REQUIRES_REMEDIATION",
        "packet_result": PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "candidate_review_outcome": CANDIDATE_REVIEW_OUTCOME,
        "candidate_review_result": CANDIDATE_REVIEW_RESULT,
        "selected_A_ck_option_class": SELECTED_A_CK_OPTION_CLASS,
        "selected_A_ck_constraint_family": SELECTED_A_CK_CONSTRAINT_FAMILY,
        "A_bridge_candidate_id": A_BRIDGE_CANDIDATE_ID,
        "A_bridge_candidate_type": A_BRIDGE_CANDIDATE_TYPE,
        "A_bridge_constraint_form": A_BRIDGE_CONSTRAINT_FORM,
        "A_bridge_constraint_equation": A_BRIDGE_CONSTRAINT_EQUATION,
        "A_bridge_field_equation_match": A_BRIDGE_FIELD_EQUATION_MATCH,
        "A_bridge_stress_energy_match": A_BRIDGE_STRESS_ENERGY_MATCH,
        "A_bridge_source_residual_match": A_BRIDGE_SOURCE_RESIDUAL_MATCH,
        "A_bridge_rule_plain_meaning": A_BRIDGE_RULE_PLAIN_MEANING,
        "A_bridge_route_alignment_sequence": A_BRIDGE_ROUTE_ALIGNMENT_SEQUENCE,
        "A_bridge_route_alignment_sequence_plain": route_sequence,
        "bridge_candidate_id": A_BRIDGE_CANDIDATE_ID,
        "bridge_candidate_type": A_BRIDGE_CANDIDATE_TYPE,
        "bridge_constraint_form": A_BRIDGE_CONSTRAINT_FORM,
        "bridge_constraint_equation": A_BRIDGE_CONSTRAINT_EQUATION,
        "bridge_admissibility_constraint_form": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        "bridge_route_field_equation_match": A_BRIDGE_FIELD_EQUATION_MATCH,
        "bridge_route_stress_energy_match": A_BRIDGE_STRESS_ENERGY_MATCH,
        "bridge_route_source_residual_match": A_BRIDGE_SOURCE_RESIDUAL_MATCH,
        "bridge_candidate_rule_plain_meaning": A_BRIDGE_RULE_PLAIN_MEANING,
        "bridge_component_count": 3,
        "source_rule_closeout_outcome": SOURCE_RULE_CLOSEOUT_OUTCOME,
        "source_candidate_constraint_id": SOURCE_CANDIDATE_CONSTRAINT_ID,
        "source_candidate_constraint_form": SOURCE_CANDIDATE_CONSTRAINT_FORM,
        "source_candidate_constraint_equation": SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
        "source_admissibility_constraint_form": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        "gauge_group_policy": GAUGE_GROUP_POLICY,
        "A_field_domain_policy": A_FIELD_DOMAIN_POLICY,
        "F_definition_policy": F_DEFINITION_POLICY,
        "bianchi_identity_route": BIANCHI_IDENTITY_ROUTE,
        "vacuum_euler_lagrange_route": VACUUM_EULER_LAGRANGE_ROUTE,
        "source_route_still_blocked": SOURCE_ROUTE_STILL_BLOCKED,
        "stress_energy_under_selected_u1_policy": STRESS_ENERGY_UNDER_SELECTED_U1_POLICY,
        "source_admissibility_condition": SOURCE_ADMISSIBILITY_CONDITION,
        "divergence_identity": DIVERGENCE_IDENTITY,
        "on_shell_vacuum_conservation_identity": ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
        "bounded_source_admissibility_result": BOUNDED_SOURCE_ADMISSIBILITY_RESULT,
        "local_source_route_scope": LOCAL_SOURCE_ROUTE_SCOPE,
        "vacuum_supporting_identity_form": VACUUM_SUPPORTING_IDENTITY_FORM,
        "vacuum_on_shell_implication_form": VACUUM_ON_SHELL_IMPLICATION_FORM,
        "embedding_routes": routes,
        "embedding_route_count": len(routes),
        "selected_embedding_route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
        "admissibility_only_route_selected": True,
        "admissibility_only_interpretation_retained": True,
        "constraint_as_admissibility_rule_selected": True,
        "route_consistency_tuple_carried_forward": True,
        "field_equation_match_component_preserved": True,
        "stress_energy_match_component_preserved": True,
        "source_residual_match_component_preserved": True,
        "source_admissibility_context_preserved": True,
        "vacuum_u1_scope_preserved": True,
        "lagrange_multiplier_route_recorded": True,
        "lagrange_multiplier_route_blocked": True,
        "lagrange_multiplier_action_form": LAGRANGE_MULTIPLIER_ACTION_FORM,
        "component_pairing_requirements": COMPONENT_PAIRING_REQUIREMENTS,
        "penalty_route_recorded": True,
        "penalty_route_unlicensed": True,
        "penalty_action_form": PENALTY_ACTION_FORM,
        "functional_embedding_packet_prepared": True,
        "functional_embedding_options_recorded": True,
        "dynamical_action_embedding_not_assumed": True,
        "review_rows": review_rows,
        "review_row_count": len(review_rows),
        "review_row_accepted_count": sum(
            1 for row in review_rows if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "proof_depth_label": (
            "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_OPTIONS_"
            "RECORDED_ADMISSIBILITY_ONLY"
        ),
        "mathematical_statement": (
            "The functional-embedding packet records three routes for the "
            "ToE-native A bridge-admissibility C_k candidate. The "
            "admissibility-only route C_bridge^A = 0 is selected as a "
            "non-dynamical vacuum U(1) route-consistency rule. The multiplier "
            "route "
            + LAGRANGE_MULTIPLIER_ACTION_FORM
            + " is blocked by unselected component pairing, multiplier "
            "domain, covariance control, boundary-term policy, variation "
            "policy, and the missing proof that it preserves intended gauge "
            "dynamics. The penalty route "
            + PENALTY_ACTION_FORM
            + " is recorded but unlicensed because no norm over the "
            "heterogeneous route tuple is defined and it would create a new "
            "dynamical penalty term. No action variation is executed."
        ),
        "non_claim_boundary": (
            "This packet records A bridge functional-embedding options and "
            "selects the admissibility-only route C_bridge^A = 0. It does not "
            "functionalize C_bridge^A, does not embed it in S_C, does not "
            "define a C_k action term, does not select Lambda_bridge or a "
            "multiplier domain, does not select a component pairing rule, "
            "does not prove covariance control, does not select a boundary-"
            "term policy, does not select a variation policy, does not prove "
            "preservation of the intended gauge dynamics, does not license "
            "the penalty route, does not define a norm over the heterogeneous "
            "route tuple, does not execute C_k variation, does not vary "
            "Lambda_bridge, A, or g, does not prove bridge admissibility, "
            "does not prove any route-match component, does not verify full "
            "route alignment, does not derive J^nu, does not derive a "
            "psi-current or external-current native route, does not derive "
            "sourced Maxwell, does not prove matter/current exchange, does "
            "not close EM, does not close QFT-GR, does not authorize "
            "semiclassical coupling, does not promote the master action, and "
            "does not claim empirical validation or public readiness."
        ),
        "critical_gate_fail_conditions": [
            "claim the multiplier route is selected as an action term",
            "claim the penalty route is licensed",
            "define a norm over the heterogeneous route tuple without a packet",
            "select Lambda_bridge multiplier type or domain",
            "select a component pairing rule",
            "claim covariance control is established",
            "execute C_k or Lambda_bridge variation",
            "execute A or metric variation of the candidate",
            "claim boundary terms are controlled",
            "claim variation policy is selected",
            "claim intended gauge dynamics are preserved by the action term",
            "claim full bridge admissibility is proved",
            "claim route alignment is verified",
            "derive J^nu",
            "derive sourced Maxwell",
            "prove matter/current exchange",
            "claim full EM closure",
            "claim QFT-GR closure",
            "claim semiclassical coupling",
            "promote the master action",
            "claim empirical validation or public readiness",
        ],
        "validation_policy": _validation_policy(),
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "aggregate_lean_validation_status_for_packet": FULL_TOEFORMAL_STATUS,
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_STATUS,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativeABridgeAdmissibilityCKFunctionalEmbeddingPacket",
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
    packet.update(_false_boundary_flags())
    return packet


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
            "Build the ToE-native A bridge-admissibility C_k functional "
            "embedding packet."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    packet = build_toe_native_a_bridge_admissibility_ck_functional_embedding_packet(
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
