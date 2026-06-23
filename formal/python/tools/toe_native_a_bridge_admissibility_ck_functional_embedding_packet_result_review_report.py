from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_a_bridge_admissibility_ck_functional_embedding_packet_report import (
    ADMISSIBILITY_ONLY_ROUTE_ID,
    A_BRIDGE_CANDIDATE_ID,
    A_BRIDGE_CANDIDATE_TYPE,
    A_BRIDGE_CONSTRAINT_EQUATION,
    A_BRIDGE_CONSTRAINT_FORM,
    A_BRIDGE_FIELD_EQUATION_MATCH,
    A_BRIDGE_SOURCE_RESIDUAL_MATCH,
    A_BRIDGE_STRESS_ENERGY_MATCH,
    A_FIELD_DOMAIN_POLICY,
    BOUNDED_SOURCE_ADMISSIBILITY_RESULT,
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    COMPONENT_PAIRING_REQUIREMENTS,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as EMBEDDING_PACKET_PATH,
    F_DEFINITION_POLICY,
    FULL_TOEFORMAL_STATUS,
    GAUGE_GROUP_POLICY,
    LAGRANGE_MULTIPLIER_ACTION_FORM,
    LAGRANGE_MULTIPLIER_ROUTE_ID,
    LEAN_PACKET_PATH as EMBEDDING_LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
    OUTCOME_ID as EMBEDDING_PACKET_OUTCOME,
    PACKET_ID as EMBEDDING_PACKET_ID,
    PACKET_RESULT as EMBEDDING_PACKET_RESULT,
    PENALTY_ACTION_FORM,
    PENALTY_ROUTE_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID as EMBEDDING_PACKET_SCHEMA_ID,
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
    "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_"
    "RESULT_REVIEW_20260622_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_"
    "RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_"
    "RESULT_REVIEW_ACCEPTS_ADMISSIBILITY_ONLY_ROUTE_NO_ACTION_VARIATION_OR_"
    "PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_A_bridge_admissibility_ck_functional_embedding_result_review_"
    "accepts_admissibility_only_route_no_action_variation_or_promotion"
)
NEXT_TARGET = "prepare_toe_native_A_bridge_admissibility_ck_admissibility_rule_closeout"
NEXT_TARGET_KIND = (
    "toe_native_A_bridge_admissibility_ck_admissibility_rule_closeout_preparation"
)
FIRST_A_BRIDGE_RULE_CLASSIFICATION = (
    "first_A_relevant_ck_vacuum_gauge_bridge_admissibility_rule_candidate"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_"
    "RESULT_REVIEW_20260622_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeABridgeAdmissibilityCKFunctionalEmbeddingPacketResultReview.lean"
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
            "evidence": packet.get("bridge_admissibility_constraint_form"),
            "assessment": (
                "The review accepts only the non-dynamical vacuum U(1) "
                "route-consistency rule."
            ),
        },
        {
            "row_id": "c_bridge_a_zero_preserved_as_rule",
            "status": "accepted",
            "evidence": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
            "assessment": (
                "C_bridge^A = 0 is preserved as an admissibility rule, not "
                "as an action term or dynamical law."
            ),
        },
        {
            "row_id": "bridge_tuple_context_preserved",
            "status": "accepted",
            "evidence": [
                A_BRIDGE_CONSTRAINT_FORM,
                A_BRIDGE_FIELD_EQUATION_MATCH,
                A_BRIDGE_STRESS_ENERGY_MATCH,
                A_BRIDGE_SOURCE_RESIDUAL_MATCH,
            ],
            "assessment": (
                "The bridge tuple and its route-match components are carried "
                "forward only as preserved context."
            ),
        },
        {
            "row_id": "source_and_vacuum_u1_context_preserved",
            "status": "accepted",
            "evidence": [
                SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
                GAUGE_GROUP_POLICY,
                A_FIELD_DOMAIN_POLICY,
                F_DEFINITION_POLICY,
                VACUUM_EULER_LAGRANGE_ROUTE,
                SOURCE_ROUTE_STILL_BLOCKED,
            ],
            "assessment": "The bounded local classical vacuum U(1) source context is preserved.",
        },
        {
            "row_id": "multiplier_action_route_blocked",
            "status": "accepted",
            "evidence": LAGRANGE_MULTIPLIER_ACTION_FORM,
            "assessment": (
                "The multiplier/action route remains blocked by unselected "
                "component pairing, multiplier domain, covariance control, "
                "boundary policy, variation policy, and gauge-dynamics "
                "preservation proof."
            ),
        },
        {
            "row_id": "penalty_route_unlicensed",
            "status": "accepted",
            "evidence": PENALTY_ACTION_FORM,
            "assessment": (
                "The penalty route remains unlicensed because no norm over "
                "the heterogeneous route tuple is defined and it would add a "
                "new dynamical penalty term."
            ),
        },
        {
            "row_id": "no_bridge_proof_or_route_alignment",
            "status": "accepted",
            "evidence": [
                "bridge_admissibility_proved=false",
                "route_consistency_tuple_proved=false",
                "field_equation_match_proved=false",
                "stress_energy_match_proved=false",
                "source_residual_match_proved=false",
            ],
            "assessment": "No bridge proof or route-alignment proof is claimed.",
        },
        {
            "row_id": "no_ck_action_embedding_or_variation",
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
            "row_id": "no_current_sourced_maxwell_or_exchange",
            "status": "accepted",
            "evidence": [
                "J_nu_derived=false",
                "psi_current_route_constructed=false",
                "external_current_native_derivation_selected=false",
                "sourced_maxwell_equation_derived=false",
                "matter_current_exchange_route_proved=false",
            ],
            "assessment": "No current, sourced Maxwell route, or matter/current exchange is introduced.",
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
            "assessment": "EM closure, QFT-GR closure, coupling, validation, and promotion remain blocked.",
        },
        {
            "row_id": "admissibility_rule_closeout_next_target_selected",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next bounded target is the A bridge-admissibility rule closeout.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "toe_native_A_bridge_admissibility_ck_functional_embedding_packet_"
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


def build_toe_native_a_bridge_admissibility_ck_functional_embedding_packet_result_review(
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
            and packet.get("bridge_admissibility_constraint_form")
            == BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "bridge_tuple_forms_exact": (
            packet.get("A_bridge_candidate_id") == A_BRIDGE_CANDIDATE_ID
            and packet.get("A_bridge_candidate_type") == A_BRIDGE_CANDIDATE_TYPE
            and packet.get("A_bridge_constraint_form") == A_BRIDGE_CONSTRAINT_FORM
            and packet.get("A_bridge_constraint_equation")
            == A_BRIDGE_CONSTRAINT_EQUATION
            and packet.get("A_bridge_field_equation_match")
            == A_BRIDGE_FIELD_EQUATION_MATCH
            and packet.get("A_bridge_stress_energy_match")
            == A_BRIDGE_STRESS_ENERGY_MATCH
            and packet.get("A_bridge_source_residual_match")
            == A_BRIDGE_SOURCE_RESIDUAL_MATCH
        ),
        "source_and_vacuum_context_exact": (
            packet.get("source_rule_closeout_outcome") == SOURCE_RULE_CLOSEOUT_OUTCOME
            and packet.get("source_candidate_constraint_id")
            == SOURCE_CANDIDATE_CONSTRAINT_ID
            and packet.get("source_candidate_constraint_form")
            == SOURCE_CANDIDATE_CONSTRAINT_FORM
            and packet.get("source_candidate_constraint_equation")
            == SOURCE_CANDIDATE_CONSTRAINT_EQUATION
            and packet.get("source_admissibility_constraint_form")
            == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
            and packet.get("gauge_group_policy") == GAUGE_GROUP_POLICY
            and packet.get("A_field_domain_policy") == A_FIELD_DOMAIN_POLICY
            and packet.get("F_definition_policy") == F_DEFINITION_POLICY
            and packet.get("vacuum_euler_lagrange_route")
            == VACUUM_EULER_LAGRANGE_ROUTE
            and packet.get("source_route_still_blocked") == SOURCE_ROUTE_STILL_BLOCKED
        ),
        "action_routes_blocked_or_unlicensed": (
            packet.get("lagrange_multiplier_route_recorded") is True
            and packet.get("lagrange_multiplier_route_blocked") is True
            and packet.get("lagrange_multiplier_action_form")
            == LAGRANGE_MULTIPLIER_ACTION_FORM
            and packet.get("component_pairing_requirements")
            == COMPONENT_PAIRING_REQUIREMENTS
            and packet.get("penalty_route_recorded") is True
            and packet.get("penalty_route_unlicensed") is True
            and packet.get("penalty_route_licensed") is False
            and packet.get("penalty_action_form") == PENALTY_ACTION_FORM
        ),
        "no_bridge_proof_or_route_alignment": all(
            packet.get(key) is False
            for key in [
                "bridge_proof_claimed",
                "bridge_admissibility_proved",
                "A_bridge_admissibility_proved",
                "bridge_route_alignment_verified",
                "route_consistency_tuple_proved",
                "field_equation_match_proved",
                "stress_energy_match_proved",
                "source_residual_match_proved",
            ]
        ),
        "no_action_embedding_or_variation": all(
            packet.get(key) is False
            for key in [
                "dynamical_action_embedding_selected",
                "constraint_as_action_term_selected",
                "constraint_multiplier_type_selected",
                "constraint_term_selected",
                "multiplier_domain_selected",
                "component_pairing_rule_selected",
                "covariance_control_established",
                "boundary_term_policy_selected",
                "boundary_terms_controlled",
                "variation_policy_selected",
                "gauge_dynamics_preservation_proved",
                "heterogeneous_tuple_norm_defined",
                "quadratic_penalty_route_licensed",
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
            packet.get(key) is False
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
            packet.get(key) is False
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
        else "REMEDIATE_TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_REVIEW"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_"
            "PACKET_RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "review_prepared": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_REVIEW_REQUIRES_REMEDIATION",
        "packet_result": "REVIEW_ACCEPTED" if accepted else "REVIEW_REQUIRES_REMEDIATION",
        "review_result": REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "embedding_packet_outcome": EMBEDDING_PACKET_OUTCOME,
        "embedding_packet_result": EMBEDDING_PACKET_RESULT,
        "selected_A_ck_option_class": SELECTED_A_CK_OPTION_CLASS,
        "selected_A_ck_constraint_family": SELECTED_A_CK_CONSTRAINT_FAMILY,
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
        "bounded_source_admissibility_result": BOUNDED_SOURCE_ADMISSIBILITY_RESULT,
        "embedding_route_count": 3,
        "selected_embedding_route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
        "admissibility_only_route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
        "bridge_admissibility_route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
        "lagrange_multiplier_route_id": LAGRANGE_MULTIPLIER_ROUTE_ID,
        "lagrange_multiplier_action_form": LAGRANGE_MULTIPLIER_ACTION_FORM,
        "penalty_route_id": PENALTY_ROUTE_ID,
        "penalty_action_form": PENALTY_ACTION_FORM,
        "functional_embedding_result_review_prepared": True,
        "functional_embedding_result_review_accepted": True,
        "review_accepts_admissibility_only_route": True,
        "packet_result_review_accepts_admissibility_only_route": True,
        "admissibility_rule_closeout_authorized": True,
        "admissibility_rule_closeout_prepared": False,
        "first_A_relevant_ck_admissibility_rule_candidate_classification": (
            FIRST_A_BRIDGE_RULE_CLASSIFICATION
        ),
        "functional_embedding_packet_prepared": True,
        "functional_embedding_options_recorded": True,
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
        "penalty_route_recorded": True,
        "penalty_route_unlicensed": True,
        "dynamical_action_embedding_not_assumed": True,
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
        "dynamical_action_embedding_selected": False,
        "constraint_as_action_term_selected": False,
        "constraint_multiplier_type_selected": False,
        "constraint_term_selected": False,
        "multiplier_domain_selected": False,
        "component_pairing_rule_selected": False,
        "covariance_control_established": False,
        "boundary_term_policy_selected": False,
        "boundary_terms_controlled": False,
        "variation_policy_selected": False,
        "gauge_dynamics_preservation_proved": False,
        "heterogeneous_tuple_norm_defined": False,
        "penalty_route_licensed": False,
        "quadratic_penalty_route_licensed": False,
        "fully_concrete_ck_functional_selected": False,
        "fully_concrete_ck_functional_defined": False,
        "concrete_ck_functional_selected": False,
        "concrete_ck_functional_defined": False,
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
        "review_criteria": criteria,
        "review_criteria_count": len(criteria),
        "review_criteria_accepted_count": sum(
            1 for row in criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "proof_depth_label": (
            "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_REVIEW_"
            "ACCEPTS_ADMISSIBILITY_ONLY"
        ),
        "mathematical_statement": (
            "The review accepts the A bridge-admissibility C_k "
            "functional-embedding packet only at the admissibility-rule "
            "level. The rule C_bridge^A = 0 is preserved as a "
            "non-dynamical vacuum U(1) route-consistency condition. The "
            "multiplier/action route remains blocked, the penalty route "
            "remains unlicensed, and no action variation or promotion is "
            "executed."
        ),
        "non_claim_boundary": (
            "This review accepts the admissibility-only route as a rule only, "
            "not as an action term. It preserves C_bridge^A = 0 as a vacuum "
            "U(1) route-consistency admissibility rule, keeps the "
            "multiplier/action route blocked by missing component pairing, "
            "multiplier domain, covariance control, boundary-term policy, "
            "variation policy, and unproved preservation of intended gauge "
            "dynamics, and keeps the penalty route unlicensed. It does not "
            "functionalize C_bridge^A, does not embed it in S_C, does not "
            "define a C_k action term, does not select Lambda_bridge or a "
            "multiplier domain, does not select a component pairing rule, "
            "does not prove covariance control, does not select a boundary-"
            "term policy, does not select a variation policy, does not prove "
            "preservation of the intended gauge dynamics, does not license the "
            "penalty route, does not define a norm over the heterogeneous "
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
            "treat C_bridge^A = 0 as a selected dynamical action term",
            "claim the multiplier/action route is selected",
            "claim the penalty route is licensed",
            "define a norm over the heterogeneous route tuple without a packet",
            "select Lambda_bridge multiplier type or domain",
            "select a component pairing rule",
            "execute C_k or Lambda_bridge variation",
            "execute A or metric variation of the candidate",
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
            "claim empirical validation or public readiness",
        ],
        "validation_policy": _validation_policy(),
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "aggregate_lean_validation_status_for_packet": FULL_TOEFORMAL_STATUS,
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_STATUS,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativeABridgeAdmissibilityCKFunctionalEmbeddingPacketResultReview",
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
            "embedding_lean_packet_file": _ptr(EMBEDDING_LEAN_PACKET_PATH),
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
            "Build the ToE-native A bridge-admissibility C_k "
            "functional-embedding packet result review."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    review = (
        build_toe_native_a_bridge_admissibility_ck_functional_embedding_packet_result_review(
            captured_at_utc=args.captured_at_utc
        )
    )
    write_review(review, args.out)


if __name__ == "__main__":
    main()
