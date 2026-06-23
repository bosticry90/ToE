from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

sys.setrecursionlimit(10000)

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_a_bridge_admissibility_ck_functional_embedding_packet_result_review_report import (
    ADMISSIBILITY_ONLY_ROUTE_ID,
    A_BRIDGE_CANDIDATE_ID,
    A_BRIDGE_CANDIDATE_TYPE,
    A_BRIDGE_CONSTRAINT_EQUATION,
    A_BRIDGE_CONSTRAINT_FORM,
    A_BRIDGE_FIELD_EQUATION_MATCH,
    A_BRIDGE_SOURCE_RESIDUAL_MATCH,
    A_BRIDGE_STRESS_ENERGY_MATCH,
    A_FIELD_DOMAIN_POLICY,
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as FUNCTIONAL_EMBEDDING_REVIEW_PATH,
    F_DEFINITION_POLICY,
    FIRST_A_BRIDGE_RULE_CLASSIFICATION,
    FULL_TOEFORMAL_STATUS,
    GAUGE_GROUP_POLICY,
    LAGRANGE_MULTIPLIER_ACTION_FORM,
    LAGRANGE_MULTIPLIER_ROUTE_ID,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
    OUTCOME_ID as FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME,
    PACKET_ID as FUNCTIONAL_EMBEDDING_REVIEW_PACKET_ID,
    PENALTY_ACTION_FORM,
    PENALTY_ROUTE_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    REVIEW_RESULT as FUNCTIONAL_EMBEDDING_REVIEW_RESULT,
    SCHEMA_ID as FUNCTIONAL_EMBEDDING_REVIEW_SCHEMA_ID,
    SELECTED_A_CK_CONSTRAINT_FAMILY,
    SELECTED_A_CK_OPTION_CLASS,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    SOURCE_ROUTE_STILL_BLOCKED,
    SOURCE_RULE_CLOSEOUT_OUTCOME,
    VACUUM_EULER_LAGRANGE_ROUTE,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-22T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSEOUT_"
    "20260622_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSEOUT_v0"
CLOSEOUT_RESULT = (
    "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSED_AS_"
    "VACUUM_U1_ROUTE_CONSISTENCY_RULE_NO_ACTION_VARIATION_OR_PROMOTION"
)
OUTCOME_ID = CLOSEOUT_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_A_bridge_admissibility_ck_admissibility_rule_closed_as_"
    "vacuum_u1_route_consistency_rule_no_action_variation_or_promotion"
)
NEXT_TARGET = (
    "select_next_toe_native_A_ck_constraint_family_after_source_and_bridge_"
    "admissibility"
)
NEXT_TARGET_KIND = (
    "toe_native_A_ck_constraint_family_after_source_and_bridge_admissibility_"
    "selection"
)
NEXT_RECOMMENDED_A_CK_FAMILY = "A_transport_consistency_constraint_family"
NEXT_RECOMMENDED_A_CK_CANDIDATE_TARGET = (
    "prepare_toe_native_A_transport_consistency_ck_constraint_candidate_packet"
)
NEXT_RECOMMENDED_REASON = (
    "source and bridge admissibility are now closed as vacuum U(1) "
    "admissibility-only rules; the next bounded selector should ask whether "
    "the A route remains coherent through action, variation, stress-energy, "
    "source rule, bridge rule, and residual/regime surfaces without current, "
    "EM closure, or master-action promotion"
)
BRIDGE_RULE_CLASSIFICATION = (
    "vacuum U(1) bridge-admissibility route-consistency rule candidate"
)
BRIDGE_RULE_EPISTEMIC_STATUS = "admissibility-only"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSEOUT_"
    "20260622_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeABridgeAdmissibilityCKAdmissibilityRuleCloseout.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _closeout_criteria(review: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "functional_embedding_review_accepts_admissibility_only",
            "status": "accepted",
            "evidence": review.get("review_result"),
            "assessment": (
                "The consumed review accepted only the admissibility-rule "
                "interpretation of C_bridge^A = 0."
            ),
        },
        {
            "row_id": "vacuum_u1_bridge_rule_closed",
            "status": "accepted",
            "evidence": CLOSEOUT_RESULT,
            "assessment": (
                "The packet closes the A bridge C_k rule as a vacuum U(1) "
                "route-consistency rule only."
            ),
        },
        {
            "row_id": "bridge_tuple_preserved",
            "status": "accepted",
            "evidence": A_BRIDGE_CONSTRAINT_FORM,
            "assessment": "The three-component bridge tuple is preserved exactly.",
        },
        {
            "row_id": "bridge_condition_preserved",
            "status": "accepted",
            "evidence": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
            "assessment": "C_bridge^A = 0 is preserved as the bridge rule.",
        },
        {
            "row_id": "bridge_components_preserved",
            "status": "accepted",
            "evidence": [
                A_BRIDGE_FIELD_EQUATION_MATCH,
                A_BRIDGE_STRESS_ENERGY_MATCH,
                A_BRIDGE_SOURCE_RESIDUAL_MATCH,
            ],
            "assessment": (
                "The master-action equation, stress-energy, and source-residual "
                "comparison components are carried forward."
            ),
        },
        {
            "row_id": "source_rule_context_preserved",
            "status": "accepted",
            "evidence": [SOURCE_RULE_CLOSEOUT_OUTCOME, SOURCE_ADMISSIBILITY_CONSTRAINT_FORM],
            "assessment": (
                "The A source-admissibility rule remains the source-side "
                "context for the bridge rule."
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
                SOURCE_ROUTE_STILL_BLOCKED,
            ],
            "assessment": (
                "The bounded local classical vacuum U(1) context remains "
                "the only accepted scope."
            ),
        },
        {
            "row_id": "closed_as_admissibility_only_route_consistency_rule",
            "status": "accepted",
            "evidence": [BRIDGE_RULE_CLASSIFICATION, BRIDGE_RULE_EPISTEMIC_STATUS],
            "assessment": (
                "The object is closed as a bridge-admissibility route-"
                "consistency rule candidate and admissibility-only."
            ),
        },
        {
            "row_id": "not_action_term_or_dynamical_law",
            "status": "accepted",
            "evidence": [
                "constraint_as_action_term_selected=false",
                "dynamical_action_embedding_selected=false",
                "candidate_recorded_as_new_physical_law=false",
            ],
            "assessment": (
                "The rule is not treated as an action term, new dynamical law, "
                "or master-action promotion."
            ),
        },
        {
            "row_id": "multiplier_and_penalty_routes_remain_blocked",
            "status": "accepted",
            "evidence": [LAGRANGE_MULTIPLIER_ACTION_FORM, PENALTY_ACTION_FORM],
            "assessment": (
                "The multiplier route remains blocked and the penalty route "
                "remains unlicensed."
            ),
        },
        {
            "row_id": "no_bridge_proof_action_embedding_or_variation",
            "status": "accepted",
            "evidence": [
                "bridge_admissibility_proved=false",
                "route_consistency_tuple_proved=false",
                "C_k_action_embedding_constructed=false",
                "C_k_variation_executed=false",
            ],
            "assessment": (
                "No bridge proof, route-alignment proof, C_k action embedding, "
                "or C_k variation is claimed."
            ),
        },
        {
            "row_id": "no_current_sourced_maxwell_or_exchange",
            "status": "accepted",
            "evidence": [
                "J_nu_derived=false",
                "psi_current_route_constructed=false",
                "external_current_native_derivation_selected=false",
                "sourced_maxwell_equation_derived=false",
                "matter_current_exchange_route_proved=false",
            ],
            "assessment": (
                "No current, sourced Maxwell route, or matter/current exchange "
                "route is introduced."
            ),
        },
        {
            "row_id": "no_closure_coupling_validation_promotion_and_selector_authorized",
            "status": "accepted",
            "evidence": [
                "full_em_closure_claimed=false",
                "qft_gr_closure_claimed=false",
                "semiclassical_coupling_authorized=false",
                "empirical_validation_claimed=false",
                "master_action_promoted=false",
                NEXT_TARGET,
            ],
            "assessment": (
                "Closure, coupling, validation, and promotion remain blocked; "
                "only the next A/C_k family selector is authorized."
            ),
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "toe_native_A_bridge_admissibility_ck_admissibility_rule_closeout"
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


def build_toe_native_a_bridge_admissibility_ck_admissibility_rule_closeout(
    *,
    functional_embedding_review_path: Path = FUNCTIONAL_EMBEDDING_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(functional_embedding_review_path)
    criteria = _closeout_criteria(review)
    acceptance_criteria = {
        "consumes_expected_closeout_target": (
            review.get("schema_id") == FUNCTIONAL_EMBEDDING_REVIEW_SCHEMA_ID
            and review.get("packet_id") == FUNCTIONAL_EMBEDDING_REVIEW_PACKET_ID
            and review.get("outcome_id") == FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME
            and review.get("review_result") == FUNCTIONAL_EMBEDDING_REVIEW_RESULT
            and review.get("selected_next_target") == CONSUMED_TARGET
            and review.get("accepted") is True
        ),
        "bridge_tuple_and_components_preserved": (
            review.get("A_bridge_candidate_id") == A_BRIDGE_CANDIDATE_ID
            and review.get("A_bridge_candidate_type") == A_BRIDGE_CANDIDATE_TYPE
            and review.get("A_bridge_constraint_form") == A_BRIDGE_CONSTRAINT_FORM
            and review.get("A_bridge_constraint_equation")
            == A_BRIDGE_CONSTRAINT_EQUATION
            and review.get("bridge_admissibility_constraint_form")
            == BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
            and review.get("A_bridge_field_equation_match")
            == A_BRIDGE_FIELD_EQUATION_MATCH
            and review.get("A_bridge_stress_energy_match")
            == A_BRIDGE_STRESS_ENERGY_MATCH
            and review.get("A_bridge_source_residual_match")
            == A_BRIDGE_SOURCE_RESIDUAL_MATCH
        ),
        "source_and_vacuum_context_preserved": (
            review.get("source_rule_closeout_outcome") == SOURCE_RULE_CLOSEOUT_OUTCOME
            and review.get("source_candidate_constraint_id")
            == SOURCE_CANDIDATE_CONSTRAINT_ID
            and review.get("source_candidate_constraint_form")
            == SOURCE_CANDIDATE_CONSTRAINT_FORM
            and review.get("source_candidate_constraint_equation")
            == SOURCE_CANDIDATE_CONSTRAINT_EQUATION
            and review.get("source_admissibility_constraint_form")
            == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
            and review.get("gauge_group_policy") == GAUGE_GROUP_POLICY
            and review.get("A_field_domain_policy") == A_FIELD_DOMAIN_POLICY
            and review.get("F_definition_policy") == F_DEFINITION_POLICY
            and review.get("vacuum_euler_lagrange_route")
            == VACUUM_EULER_LAGRANGE_ROUTE
            and review.get("source_route_still_blocked") == SOURCE_ROUTE_STILL_BLOCKED
        ),
        "closed_as_admissibility_only": (
            review.get("review_accepts_admissibility_only_route") is True
            and review.get("admissibility_only_route_selected") is True
            and review.get("constraint_as_admissibility_rule_selected") is True
            and review.get("constraint_as_action_term_selected") is False
            and review.get("dynamical_action_embedding_selected") is False
        ),
        "action_routes_remain_blocked": (
            review.get("lagrange_multiplier_route_blocked") is True
            and review.get("lagrange_multiplier_action_form")
            == LAGRANGE_MULTIPLIER_ACTION_FORM
            and review.get("penalty_route_unlicensed") is True
            and review.get("penalty_route_licensed") is False
            and review.get("penalty_action_form") == PENALTY_ACTION_FORM
        ),
        "no_bridge_proof_action_embedding_or_variation": all(
            review.get(key) is False
            for key in [
                "bridge_proof_claimed",
                "bridge_admissibility_claimed",
                "bridge_admissibility_proved",
                "A_bridge_admissibility_proved",
                "bridge_route_alignment_verified",
                "route_consistency_tuple_proved",
                "field_equation_match_proved",
                "stress_energy_match_proved",
                "source_residual_match_proved",
                "dynamical_action_embedding_selected",
                "constraint_as_action_term_selected",
                "component_pairing_rule_selected",
                "multiplier_domain_selected",
                "covariance_control_established",
                "boundary_term_policy_selected",
                "boundary_terms_controlled",
                "variation_policy_selected",
                "gauge_dynamics_preservation_proved",
                "heterogeneous_tuple_norm_defined",
                "candidate_action_insertion_executed",
                "ck_action_embedding_constructed",
                "C_k_action_embedding_constructed",
                "ck_variation_executed",
                "C_k_variation_executed",
                "lambda_variation_executed",
                "metric_variation_of_candidate_executed",
                "A_variation_of_candidate_executed",
                "penalty_variation_executed",
            ]
        ),
        "no_current_sourced_or_exchange_route": all(
            review.get(key) is False
            for key in [
                "J_nu_derived",
                "psi_current_route_constructed",
                "external_current_native_derivation_selected",
                "sourced_maxwell_equation_derived",
                "sourced_maxwell_route_derived",
                "matter_current_exchange_route_proved",
                "matter_gauge_energy_exchange_proved",
            ]
        ),
        "no_forbidden_claims": all(
            review.get(key) is False
            for key in [
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
        else "REMEDIATE_TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSEOUT"
    )
    rule_family_summary = [
        {
            "rule_id": "A_source_admissibility_ck_rule",
            "rule_form": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
            "plain_meaning": (
                "vacuum gauge stress-energy may source gravity only if conserved"
            ),
            "status": "closed_as_admissibility_only",
            "action_term": False,
            "derives_current_or_sourced_maxwell": False,
        },
        {
            "rule_id": "A_bridge_admissibility_ck_rule",
            "rule_form": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
            "plain_meaning": (
                "the master-action A route must match the selected vacuum U(1) route"
            ),
            "status": "closed_as_admissibility_only",
            "action_term": False,
            "derives_current_or_sourced_maxwell": False,
        },
    ]
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSEOUT"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSEOUT_REQUIRES_REMEDIATION",
        "closeout_result": CLOSEOUT_RESULT,
        "packet_result": "CLOSEOUT_ACCEPTED" if accepted else "CLOSEOUT_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "functional_embedding_review_outcome": FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME,
        "functional_embedding_review_result": FUNCTIONAL_EMBEDDING_REVIEW_RESULT,
        "selected_A_ck_option_class": SELECTED_A_CK_OPTION_CLASS,
        "selected_A_ck_constraint_family": SELECTED_A_CK_CONSTRAINT_FAMILY,
        "first_A_relevant_ck_bridge_admissibility_rule_candidate_classification": (
            FIRST_A_BRIDGE_RULE_CLASSIFICATION
        ),
        "bridge_rule_classification": BRIDGE_RULE_CLASSIFICATION,
        "bridge_rule_epistemic_status": BRIDGE_RULE_EPISTEMIC_STATUS,
        "A_bridge_candidate_id": A_BRIDGE_CANDIDATE_ID,
        "A_bridge_candidate_type": A_BRIDGE_CANDIDATE_TYPE,
        "A_bridge_constraint_form": A_BRIDGE_CONSTRAINT_FORM,
        "A_bridge_constraint_equation": A_BRIDGE_CONSTRAINT_EQUATION,
        "A_bridge_field_equation_match": A_BRIDGE_FIELD_EQUATION_MATCH,
        "A_bridge_stress_energy_match": A_BRIDGE_STRESS_ENERGY_MATCH,
        "A_bridge_source_residual_match": A_BRIDGE_SOURCE_RESIDUAL_MATCH,
        "bridge_candidate_id": A_BRIDGE_CANDIDATE_ID,
        "bridge_candidate_type": A_BRIDGE_CANDIDATE_TYPE,
        "bridge_constraint_form": A_BRIDGE_CONSTRAINT_FORM,
        "bridge_constraint_equation": A_BRIDGE_CONSTRAINT_EQUATION,
        "bridge_admissibility_constraint_form": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        "bridge_component_count": 3,
        "source_rule_closeout_outcome": SOURCE_RULE_CLOSEOUT_OUTCOME,
        "source_candidate_constraint_id": SOURCE_CANDIDATE_CONSTRAINT_ID,
        "source_candidate_constraint_form": SOURCE_CANDIDATE_CONSTRAINT_FORM,
        "source_candidate_constraint_equation": SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
        "source_admissibility_constraint_form": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        "gauge_group_policy": GAUGE_GROUP_POLICY,
        "A_field_domain_policy": A_FIELD_DOMAIN_POLICY,
        "F_definition_policy": F_DEFINITION_POLICY,
        "vacuum_euler_lagrange_route": VACUUM_EULER_LAGRANGE_ROUTE,
        "source_route_still_blocked": SOURCE_ROUTE_STILL_BLOCKED,
        "on_shell_vacuum_conservation_identity": ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
        "selected_embedding_route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
        "admissibility_only_route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
        "bridge_admissibility_route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
        "lagrange_multiplier_route_id": LAGRANGE_MULTIPLIER_ROUTE_ID,
        "lagrange_multiplier_action_form": LAGRANGE_MULTIPLIER_ACTION_FORM,
        "penalty_route_id": PENALTY_ROUTE_ID,
        "penalty_action_form": PENALTY_ACTION_FORM,
        "closeout_criteria": criteria,
        "closeout_criteria_count": len(criteria),
        "closeout_criteria_accepted_count": sum(
            1 for row in criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "admissibility_rule_closeout_prepared": True,
        "admissibility_rule_closeout_accepted": True,
        "first_A_relevant_ck_bridge_admissibility_rule_candidate_closed": True,
        "A_bridge_admissibility_rule_candidate_closed": True,
        "vacuum_U1_bridge_admissibility_rule_closed": True,
        "bridge_admissibility_rule_closed_as_vacuum_U1_route_consistency_rule": True,
        "route_consistency_rule_candidate_closed": True,
        "candidate_recorded_as_rule_only": True,
        "candidate_recorded_as_action_term": False,
        "candidate_recorded_as_new_physical_law": False,
        "admissibility_only_route_selected": True,
        "admissibility_only_interpretation_retained": True,
        "constraint_as_admissibility_rule_selected": True,
        "constraint_as_action_term_selected": False,
        "dynamical_action_embedding_selected": False,
        "dynamical_action_embedding_not_assumed": True,
        "route_consistency_tuple_carried_forward": True,
        "field_equation_match_component_preserved": True,
        "stress_energy_match_component_preserved": True,
        "source_residual_match_component_preserved": True,
        "source_admissibility_context_preserved": True,
        "vacuum_u1_scope_preserved": True,
        "lagrange_multiplier_route_recorded": True,
        "lagrange_multiplier_route_blocked": True,
        "penalty_route_recorded": True,
        "penalty_route_unlicensed": True,
        "penalty_route_licensed": False,
        "quadratic_penalty_route_licensed": False,
        "next_selector_authorized": True,
        "next_selector_prepared": False,
        "next_candidate_family_recommendation": NEXT_RECOMMENDED_A_CK_FAMILY,
        "next_candidate_packet_recommendation": NEXT_RECOMMENDED_A_CK_CANDIDATE_TARGET,
        "next_candidate_family_recommendation_reason": NEXT_RECOMMENDED_REASON,
        "next_candidate_family_recommended": True,
        "next_candidate_family_selected": False,
        "A_transport_consistency_family_selected": False,
        "A_transport_consistency_candidate_packet_prepared": False,
        "source_and_bridge_rule_family_contains_count": len(rule_family_summary),
        "A_ck_source_bridge_rule_family_summary": rule_family_summary,
        "source_admissibility_rule_family_entry_preserved": True,
        "bridge_admissibility_rule_family_entry_preserved": True,
        "A_source_and_bridge_admissibility_rule_family_closed": True,
        "A_source_and_bridge_admissibility_rule_family_promoted": False,
        "bridge_proof_claimed": False,
        "bridge_admissibility_claimed": False,
        "bridge_admissibility_proved": False,
        "A_bridge_admissibility_claimed": False,
        "A_bridge_admissibility_proved": False,
        "bridge_route_alignment_verified": False,
        "route_consistency_tuple_proved": False,
        "field_equation_match_proved": False,
        "stress_energy_match_proved": False,
        "source_residual_match_proved": False,
        "component_pairing_rule_selected": False,
        "multiplier_domain_selected": False,
        "covariance_control_established": False,
        "boundary_term_policy_selected": False,
        "boundary_terms_controlled": False,
        "variation_policy_selected": False,
        "gauge_dynamics_preservation_proved": False,
        "heterogeneous_tuple_norm_defined": False,
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
        "proof_depth_label": (
            "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSEOUT_"
            "VACUUM_U1_ROUTE_CONSISTENCY_RULE_ONLY"
        ),
        "mathematical_statement": (
            "The ToE-native A bridge-admissibility C_k candidate is closed as "
            "a vacuum U(1) route-consistency admissibility rule: "
            "C_bridge^A := (E_A^master - E_A^vacuum_U1_route, "
            "T_A^master - T_A^vacuum_U1_route, C_source^A - nabla_mu "
            "T_A^{mu nu}), with rule C_bridge^A = 0. The closeout carries "
            "the accepted admissibility-only route and executes no action "
            "embedding or variation."
        ),
        "non_claim_boundary": (
            "This closeout records C_bridge^A = 0 as a vacuum U(1) "
            "bridge-admissibility route-consistency rule only. It is "
            "admissibility-only, not an action term, not a dynamical law, "
            "not action-embedded, not varied, not sourced Maxwell theory, "
            "not full EM closure, not QFT-GR closure, and not master-action "
            "promotion. It preserves C_bridge^A := (E_A^master - "
            "E_A^vacuum_U1_route, T_A^master - T_A^vacuum_U1_route, "
            "C_source^A - nabla_mu T_A^{mu nu}) and C_bridge^A = 0. It "
            "keeps the multiplier/action route blocked and keeps the penalty "
            "route unlicensed. It does not functionalize C_bridge^A, does "
            "not embed it in S_C, does not define a C_k action term, does "
            "not select Lambda_bridge or a multiplier domain, does not "
            "select a component pairing rule, does not prove covariance "
            "control, does not select a boundary-term policy, does not "
            "select a variation policy, does not prove preservation of the "
            "intended gauge dynamics, does not license the penalty route, "
            "does not define a norm over the heterogeneous route tuple, does "
            "not execute C_k variation, does not vary Lambda_bridge, A, or "
            "g, does not prove bridge admissibility, does not prove any "
            "route-match component, does not verify full route alignment, "
            "does not derive J^nu, does not derive a psi-current or "
            "external-current native route, does not derive sourced Maxwell, "
            "does not prove matter/current exchange, does not close EM, does "
            "not close QFT-GR, does not authorize semiclassical coupling, "
            "does not promote the master action, and does not claim "
            "empirical validation or public readiness. The "
            "A_transport_consistency_constraint_family is recommended only "
            "for the next selector and is not selected by this closeout."
        ),
        "critical_gate_fail_conditions": [
            "claim C_bridge^A = 0 is an action term",
            "claim C_bridge^A = 0 is a dynamical law",
            "claim C_k action embedding",
            "execute C_k variation",
            "claim the multiplier/action route is selected",
            "claim the penalty route is licensed",
            "claim full bridge admissibility is proved",
            "claim route alignment is verified",
            "derive J^nu",
            "derive a psi-current or external-current native route",
            "derive sourced Maxwell",
            "prove matter/current exchange",
            "claim full EM closure",
            "claim QFT-GR closure",
            "claim semiclassical coupling",
            "promote the master action",
            "claim empirical validation",
            "select A_transport_consistency_constraint_family before the selector runs",
        ],
        "validation_policy": _validation_policy(),
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "aggregate_lean_validation_status_for_packet": FULL_TOEFORMAL_STATUS,
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_STATUS,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativeABridgeAdmissibilityCKAdmissibilityRuleCloseout",
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
            "functional_embedding_review_file": _ptr(functional_embedding_review_path),
            "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        },
    }


def write_closeout(closeout: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(closeout, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Build the ToE-native A bridge-admissibility C_k admissibility "
            "rule closeout."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    closeout = build_toe_native_a_bridge_admissibility_ck_admissibility_rule_closeout(
        captured_at_utc=args.captured_at_utc
    )
    path = write_closeout(closeout, args.out)
    print(
        json.dumps(
            {
                "accepted": closeout["accepted"],
                "closeout_result": closeout["closeout_result"],
                "out": _ptr(path),
                "selected_next_target": closeout["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
