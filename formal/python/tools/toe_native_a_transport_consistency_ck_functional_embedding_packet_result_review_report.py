from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_a_transport_consistency_ck_functional_embedding_packet_report import (
    ADMISSIBILITY_ONLY_ROUTE_ID,
    A_BRIDGE_CONSTRAINT_EQUATION,
    A_BRIDGE_CONSTRAINT_FORM,
    A_BRIDGE_FIELD_EQUATION_MATCH,
    A_BRIDGE_SOURCE_RESIDUAL_MATCH,
    A_BRIDGE_STRESS_ENERGY_MATCH,
    A_FIELD_DOMAIN_POLICY,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as EMBEDDING_PACKET_PATH,
    DIRECT_DYNAMICAL_LAW_BLOCKING_REASONS,
    DIRECT_DYNAMICAL_LAW_INTERPRETATION_ID,
    DIRECT_DYNAMICAL_LAW_INTERPRETATION_STATUS,
    F_DEFINITION_POLICY,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    GAUGE_GROUP_POLICY,
    KNOWN_A_TRANSPORT_CHAIN_FORM,
    KNOWN_A_TRANSPORT_CHAIN_STEPS,
    LAGRANGE_MULTIPLIER_ACTION_FORM,
    LAGRANGE_MULTIPLIER_ROUTE_ID,
    LAGRANGE_MULTIPLIER_ROUTE_STATUS,
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
    PENALTY_ROUTE_STATUS,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID as EMBEDDING_PACKET_SCHEMA_ID,
    SELECTED_A_CK_CONSTRAINT_FAMILY,
    SELECTED_A_CK_OPTION_CLASS,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    SOURCE_ROUTE_STILL_BLOCKED,
    SOURCE_RULE_CLOSEOUT_OUTCOME,
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
    VACUUM_EULER_LAGRANGE_ROUTE,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-23T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_PACKET_"
    "RESULT_REVIEW_20260623_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_PACKET_"
    "RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_"
    "RESULT_REVIEW_ACCEPTS_ADMISSIBILITY_ONLY_ROUTE_NO_ACTION_VARIATION_OR_"
    "PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_A_transport_consistency_ck_functional_embedding_result_review_"
    "accepts_admissibility_only_route_no_action_variation_or_promotion"
)
NEXT_TARGET = "prepare_toe_native_A_transport_consistency_ck_admissibility_rule_closeout"
NEXT_TARGET_KIND = (
    "toe_native_A_transport_consistency_ck_admissibility_rule_closeout_preparation"
)
THIRD_A_TRANSPORT_RULE_CLASSIFICATION = (
    "third_A_relevant_ck_vacuum_u1_transport_consistency_rule_candidate"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_PACKET_"
    "RESULT_REVIEW_20260623_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeATransportConsistencyCKFunctionalEmbeddingPacketResultReview.lean"
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
            "row_id": "c_transport_a_zero_preserved",
            "status": "accepted",
            "evidence": TRANSPORT_CONSTRAINT_EQUATION,
            "assessment": "C_transport^A = 0 is preserved.",
        },
        {
            "row_id": "transport_tuple_preserved",
            "status": "accepted",
            "evidence": TRANSPORT_CONSTRAINT_FORM,
            "assessment": (
                "The vacuum U(1) derivation-chain stability tuple is carried "
                "forward only as an admissibility rule."
            ),
        },
        {
            "row_id": "admissibility_only_route_selected",
            "status": "accepted",
            "evidence": packet.get("selected_embedding_route_id"),
            "assessment": (
                "The review accepts only the non-dynamical vacuum U(1) "
                "derivation-chain stability route."
            ),
        },
        {
            "row_id": "source_and_bridge_context_preserved",
            "status": "accepted",
            "evidence": [
                SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
                A_BRIDGE_CONSTRAINT_EQUATION,
            ],
            "assessment": "The closed A source and bridge rules remain context.",
        },
        {
            "row_id": "vacuum_u1_context_preserved",
            "status": "accepted",
            "evidence": [
                GAUGE_GROUP_POLICY,
                A_FIELD_DOMAIN_POLICY,
                F_DEFINITION_POLICY,
                VACUUM_EULER_LAGRANGE_ROUTE,
                SOURCE_ROUTE_STILL_BLOCKED,
            ],
            "assessment": "The bounded local classical vacuum U(1) scope is preserved.",
        },
        {
            "row_id": "multiplier_action_route_blocked",
            "status": "accepted",
            "evidence": LAGRANGE_MULTIPLIER_ACTION_FORM,
            "assessment": (
                "The multiplier/action route remains blocked by missing "
                "multiplier type, component pairing, domains/codomains, "
                "covariance, boundary/regime projection, variation policy, "
                "and scalar-density status."
            ),
        },
        {
            "row_id": "penalty_route_unlicensed",
            "status": "accepted",
            "evidence": PENALTY_ACTION_FORM,
            "assessment": (
                "The penalty route remains unlicensed because no norm over "
                "the heterogeneous transport tuple is defined."
            ),
        },
        {
            "row_id": "direct_dynamical_law_interpretation_blocked",
            "status": "accepted",
            "evidence": DIRECT_DYNAMICAL_LAW_INTERPRETATION_ID,
            "assessment": (
                "The direct dynamical-law interpretation remains blocked; "
                "C_transport^A stays admissibility-only."
            ),
        },
        {
            "row_id": "no_transport_proof_or_concrete_functional",
            "status": "accepted",
            "evidence": [
                "transport_consistency_proved=false",
                "transport_proof_claimed=false",
                "fully_concrete_ck_functional_defined=false",
                "transport_candidate_functional_defined=false",
            ],
            "assessment": (
                "No transport proof, route-chain compatibility proof, or "
                "concrete C_transport^A functional is claimed."
            ),
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
            "row_id": "no_closure_coupling_phase_validation_or_promotion",
            "status": "accepted",
            "evidence": [
                "full_em_closure_claimed=false",
                "qft_gr_closure_claimed=false",
                "semiclassical_coupling_authorized=false",
                "empirical_validation_claimed=false",
                "phase2_readiness_claim=false",
                "master_action_promoted=false",
            ],
            "assessment": (
                "EM closure, QFT-GR closure, coupling, validation, Phase 2, "
                "and promotion remain blocked."
            ),
        },
        {
            "row_id": "full_toeformal_aggregate_recorded_not_run",
            "status": "accepted",
            "evidence": FULL_TOEFORMAL_AGGREGATE_STATUS,
            "assessment": "The full ToeFormal aggregate remains recorded as NOT_RUN.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "toe_native_A_transport_consistency_ck_functional_embedding_packet_"
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
        "aggregate_lean_validation_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def _false_boundary_flags() -> dict[str, bool]:
    return {
        "admissibility_rule_closeout_prepared": False,
        "dynamical_action_embedding_selected": False,
        "constraint_as_action_term_selected": False,
        "transport_candidate_recorded_as_action_term": False,
        "transport_candidate_recorded_as_new_dynamical_law": False,
        "transport_functional_selected": False,
        "transport_candidate_functional_defined": False,
        "transport_candidate_functional_selected": False,
        "component_pairing_rule_selected": False,
        "transport_map_domains_codomains_selected": False,
        "constraint_multiplier_type_selected": False,
        "constraint_term_selected": False,
        "multiplier_type_selected": False,
        "multiplier_domain_selected": False,
        "covariance_of_multiplier_pairing_established": False,
        "boundary_terms_controlled": False,
        "boundary_regime_projection_controlled": False,
        "variation_policy_for_embedding_selected": False,
        "heterogeneous_tuple_norm_defined": False,
        "penalty_route_licensed": False,
        "direct_dynamical_law_interpretation_selected": False,
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
        "transport_candidate_rule_proved": False,
        "transport_consistency_claimed": False,
        "transport_consistency_proved": False,
        "transport_proof_claimed": False,
        "transport_components_proved": False,
        "full_route_alignment_proof_claimed": False,
        "full_route_alignment_proved": False,
        "route_chain_compatibility_proved": False,
        "source_admissibility_proved": False,
        "source_conservation_proved": False,
        "bridge_admissibility_proved": False,
        "bridge_route_alignment_verified": False,
        "route_consistency_tuple_proved": False,
        "new_conservation_proof_claimed": False,
        "new_source_admissibility_proof_claimed": False,
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


def build_toe_native_a_transport_consistency_ck_functional_embedding_packet_result_review(
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
        "transport_rule_exact": (
            packet.get("transport_candidate_id") == TRANSPORT_CANDIDATE_ID
            and packet.get("transport_candidate_type") == TRANSPORT_CANDIDATE_TYPE
            and packet.get("transport_rule_classification")
            == TRANSPORT_RULE_CLASSIFICATION
            and packet.get("transport_rule_epistemic_status")
            == TRANSPORT_RULE_EPISTEMIC_STATUS
            and packet.get("transport_constraint_form") == TRANSPORT_CONSTRAINT_FORM
            and packet.get("transport_constraint_equation")
            == TRANSPORT_CONSTRAINT_EQUATION
            and packet.get("transport_admissibility_constraint_form")
            == TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "transport_components_exact_unproved": (
            packet.get("transport_component_count") == len(TRANSPORT_COMPONENTS)
            and packet.get("transport_components_preserved") is True
            and packet.get("transport_components_proved") is False
            and packet.get("transport_component_forms")
            == [row["component_form"] for row in TRANSPORT_COMPONENTS]
        ),
        "source_bridge_context_exact": (
            packet.get("source_candidate_constraint_id")
            == SOURCE_CANDIDATE_CONSTRAINT_ID
            and packet.get("source_candidate_constraint_form")
            == SOURCE_CANDIDATE_CONSTRAINT_FORM
            and packet.get("source_admissibility_constraint_form")
            == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
            and packet.get("A_bridge_constraint_form") == A_BRIDGE_CONSTRAINT_FORM
            and packet.get("A_bridge_constraint_equation")
            == A_BRIDGE_CONSTRAINT_EQUATION
            and packet.get("bridge_admissibility_constraint_form")
            == A_BRIDGE_CONSTRAINT_EQUATION
        ),
        "bridge_components_exact": (
            packet.get("A_bridge_field_equation_match")
            == A_BRIDGE_FIELD_EQUATION_MATCH
            and packet.get("A_bridge_stress_energy_match")
            == A_BRIDGE_STRESS_ENERGY_MATCH
            and packet.get("A_bridge_source_residual_match")
            == A_BRIDGE_SOURCE_RESIDUAL_MATCH
        ),
        "vacuum_u1_context_exact": (
            packet.get("gauge_group_policy") == GAUGE_GROUP_POLICY
            and packet.get("A_field_domain_policy") == A_FIELD_DOMAIN_POLICY
            and packet.get("F_definition_policy") == F_DEFINITION_POLICY
            and packet.get("vacuum_euler_lagrange_route")
            == VACUUM_EULER_LAGRANGE_ROUTE
            and packet.get("source_route_still_blocked") == SOURCE_ROUTE_STILL_BLOCKED
        ),
        "known_transport_chain_exact": (
            packet.get("known_A_transport_chain_form")
            == KNOWN_A_TRANSPORT_CHAIN_FORM
            and packet.get("known_A_transport_chain_steps")
            == KNOWN_A_TRANSPORT_CHAIN_STEPS
        ),
        "admissibility_only_route_selected": (
            packet.get("selected_embedding_route_id") == ADMISSIBILITY_ONLY_ROUTE_ID
            and packet.get("admissibility_only_route_selected") is True
            and packet.get("constraint_as_admissibility_rule_selected") is True
            and packet.get("constraint_as_action_term_selected") is False
        ),
        "action_routes_blocked_or_unlicensed": (
            packet.get("lagrange_multiplier_route_recorded") is True
            and packet.get("lagrange_multiplier_route_blocked") is True
            and packet.get("lagrange_multiplier_action_form")
            == LAGRANGE_MULTIPLIER_ACTION_FORM
            and packet.get("penalty_route_recorded") is True
            and packet.get("penalty_route_licensed") is False
            and packet.get("penalty_action_form") == PENALTY_ACTION_FORM
        ),
        "direct_dynamical_law_blocked": (
            packet.get("direct_dynamical_law_interpretation_recorded") is True
            and packet.get("direct_dynamical_law_interpretation_blocked") is True
            and packet.get("direct_dynamical_law_interpretation_selected") is False
            and packet.get("direct_dynamical_law_interpretation_id")
            == DIRECT_DYNAMICAL_LAW_INTERPRETATION_ID
        ),
        "no_transport_proof_or_concrete_functional": all(
            packet.get(key) is False
            for key in [
                "transport_candidate_rule_proved",
                "transport_consistency_claimed",
                "transport_consistency_proved",
                "transport_proof_claimed",
                "transport_components_proved",
                "full_route_alignment_proved",
                "route_chain_compatibility_proved",
                "transport_candidate_functional_defined",
                "fully_concrete_ck_functional_defined",
            ]
        ),
        "no_action_embedding_or_variation": all(
            packet.get(key) is False
            for key in [
                "dynamical_action_embedding_selected",
                "constraint_as_action_term_selected",
                "component_pairing_rule_selected",
                "transport_map_domains_codomains_selected",
                "constraint_multiplier_type_selected",
                "heterogeneous_tuple_norm_defined",
                "C_k_action_embedding_constructed",
                "candidate_action_insertion_executed",
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
                "phase2_readiness_claim",
                "master_action_promoted",
                "master_action_promotion_authorized",
                "canonical_master_action_promoted",
                "pillar_completion_inferred",
                "seam_closure_claim",
            ]
        ),
        "criteria_all_accepted": all(row["status"] == "accepted" for row in criteria),
        "aggregate_recorded_not_run": FULL_TOEFORMAL_AGGREGATE_STATUS == "NOT_RUN",
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_REVIEW"
    )
    review: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_"
            "PACKET_RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "review_prepared": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_REVIEW_REQUIRES_REMEDIATION",
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
        "transport_candidate_id": TRANSPORT_CANDIDATE_ID,
        "transport_candidate_type": TRANSPORT_CANDIDATE_TYPE,
        "transport_rule_classification": TRANSPORT_RULE_CLASSIFICATION,
        "transport_rule_epistemic_status": TRANSPORT_RULE_EPISTEMIC_STATUS,
        "transport_constraint_form": TRANSPORT_CONSTRAINT_FORM,
        "transport_constraint_equation": TRANSPORT_CONSTRAINT_EQUATION,
        "transport_admissibility_constraint_form": (
            TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "transport_component_count": len(TRANSPORT_COMPONENTS),
        "transport_component_forms": [
            row["component_form"] for row in TRANSPORT_COMPONENTS
        ],
        "transport_components_preserved": True,
        "transport_components_proved": False,
        "transport_action_embedding_chain_form": TRANSPORT_ACTION_EMBEDDING_CHAIN_FORM,
        "known_A_transport_chain_form": KNOWN_A_TRANSPORT_CHAIN_FORM,
        "known_A_transport_chain_steps": KNOWN_A_TRANSPORT_CHAIN_STEPS,
        "source_rule_closeout_outcome": SOURCE_RULE_CLOSEOUT_OUTCOME,
        "source_candidate_constraint_id": SOURCE_CANDIDATE_CONSTRAINT_ID,
        "source_candidate_constraint_form": SOURCE_CANDIDATE_CONSTRAINT_FORM,
        "source_admissibility_constraint_form": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        "bridge_closeout_outcome": packet.get("bridge_closeout_outcome"),
        "A_bridge_constraint_form": A_BRIDGE_CONSTRAINT_FORM,
        "A_bridge_constraint_equation": A_BRIDGE_CONSTRAINT_EQUATION,
        "bridge_admissibility_constraint_form": A_BRIDGE_CONSTRAINT_EQUATION,
        "A_bridge_field_equation_match": A_BRIDGE_FIELD_EQUATION_MATCH,
        "A_bridge_stress_energy_match": A_BRIDGE_STRESS_ENERGY_MATCH,
        "A_bridge_source_residual_match": A_BRIDGE_SOURCE_RESIDUAL_MATCH,
        "gauge_group_policy": GAUGE_GROUP_POLICY,
        "A_field_domain_policy": A_FIELD_DOMAIN_POLICY,
        "F_definition_policy": F_DEFINITION_POLICY,
        "vacuum_euler_lagrange_route": VACUUM_EULER_LAGRANGE_ROUTE,
        "on_shell_vacuum_conservation_identity": (
            ON_SHELL_VACUUM_CONSERVATION_IDENTITY
        ),
        "source_route_still_blocked": SOURCE_ROUTE_STILL_BLOCKED,
        "closed_A_ck_rule_roles": [
            "source admissibility",
            "bridge admissibility",
            "transport consistency",
        ],
        "closed_A_ck_rule_roles_plain": (
            "source admissibility -> bridge admissibility -> transport consistency"
        ),
        "closed_A_ck_rule_family_count_after_review": 3,
        "third_A_relevant_ck_admissibility_rule_candidate_classification": (
            THIRD_A_TRANSPORT_RULE_CLASSIFICATION
        ),
        "embedding_route_count": 3,
        "selected_embedding_route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
        "admissibility_only_route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
        "transport_admissibility_route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
        "transport_admissibility_only_route_status": (
            "selected_non_dynamical_vacuum_u1_derivation_chain_stability_rule"
        ),
        "lagrange_multiplier_route_id": LAGRANGE_MULTIPLIER_ROUTE_ID,
        "lagrange_multiplier_route_status": LAGRANGE_MULTIPLIER_ROUTE_STATUS,
        "lagrange_multiplier_action_form": LAGRANGE_MULTIPLIER_ACTION_FORM,
        "transport_multiplier_blocking_reasons": TRANSPORT_MULTIPLIER_BLOCKING_REASONS,
        "penalty_route_id": PENALTY_ROUTE_ID,
        "penalty_route_status": PENALTY_ROUTE_STATUS,
        "penalty_action_form": PENALTY_ACTION_FORM,
        "transport_penalty_blocking_reasons": TRANSPORT_PENALTY_BLOCKING_REASONS,
        "penalty_would_change_dynamics": True,
        "direct_dynamical_law_interpretation_id": (
            DIRECT_DYNAMICAL_LAW_INTERPRETATION_ID
        ),
        "direct_dynamical_law_interpretation_status": (
            DIRECT_DYNAMICAL_LAW_INTERPRETATION_STATUS
        ),
        "direct_dynamical_law_blocking_reasons": DIRECT_DYNAMICAL_LAW_BLOCKING_REASONS,
        "functional_embedding_result_review_prepared": True,
        "functional_embedding_result_review_accepted": True,
        "review_accepts_admissibility_only_route": True,
        "packet_result_review_accepts_admissibility_only_route": True,
        "admissibility_rule_closeout_authorized": True,
        "transport_admissibility_rule_closeout_authorized": True,
        "functional_embedding_packet_prepared": True,
        "functional_embedding_options_recorded": True,
        "admissibility_only_route_selected": True,
        "admissibility_only_interpretation_retained": True,
        "constraint_as_admissibility_rule_selected": True,
        "transport_constraint_preserved": True,
        "transport_constraint_carried_forward": True,
        "transport_tuple_preserved": True,
        "transport_tuple_carried_forward": True,
        "transport_components_carried_forward": True,
        "source_and_bridge_context_preserved": True,
        "source_and_bridge_context_retained": True,
        "vacuum_u1_scope_preserved": True,
        "known_A_chain_preserved": True,
        "known_A_chain_retained": True,
        "lagrange_multiplier_route_recorded": True,
        "lagrange_multiplier_route_blocked": True,
        "penalty_route_recorded": True,
        "penalty_route_unlicensed": True,
        "direct_dynamical_law_interpretation_recorded": True,
        "direct_dynamical_law_interpretation_blocked": True,
        "dynamical_action_embedding_not_assumed": True,
        "review_criteria": criteria,
        "review_criteria_count": len(criteria),
        "review_criteria_accepted_count": sum(
            1 for row in criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "proof_depth_label": (
            "TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_REVIEW_"
            "ACCEPTS_ADMISSIBILITY_ONLY"
        ),
        "mathematical_statement": (
            "The review accepts the A transport-consistency C_k "
            "functional-embedding packet only at the admissibility-rule "
            "level. The rule C_transport^A = 0 is preserved as a "
            "non-dynamical vacuum U(1) derivation-chain stability condition. "
            "The multiplier/action route remains blocked, the penalty route "
            "remains unlicensed, direct dynamical-law interpretation remains "
            "blocked, and no action variation or promotion is executed."
        ),
        "non_claim_boundary": (
            "This review accepts the admissibility-only route C_transport^A = 0 "
            "as a rule only, not as an action term or dynamical law. It "
            "preserves C_transport^A = 0 as a vacuum U(1) derivation-chain "
            "stability admissibility rule, keeps the multiplier/action route "
            "blocked, keeps the penalty route unlicensed, and keeps direct "
            "dynamical-law interpretation blocked. It does not functionalize "
            "C_transport^A, does not embed C_transport^A into the action, does "
            "not define a C_k action term, does not select Lambda_transport or "
            "any multiplier type, does not select a component pairing rule, "
            "does not select transport-map domains/codomains, does not prove "
            "covariance of the multiplier pairing, does not control boundary "
            "or regime projection terms, does not select an embedding "
            "variation policy, does not license the penalty route, does not "
            "define a norm over the heterogeneous transport tuple, does not "
            "interpret the candidate as a direct dynamical law, does not "
            "select a fully concrete C_transport^A functional, does not define "
            "a fully concrete C_transport^A functional, does not execute C_k "
            "variation, does not vary Lambda_transport, A, or g, does not prove "
            "transport consistency, does not prove full route alignment, does "
            "not prove any transport component, does not prove source "
            "admissibility, does not prove bridge admissibility, does not "
            "derive J^nu, does not derive a psi-current route, does not derive "
            "an external-current native route, does not derive sourced Maxwell, "
            "does not prove matter/current exchange, does not close EM, does "
            "not close QFT-GR, does not authorize semiclassical coupling, does "
            "not authorize Phase 2, records no Phase 2 authorization, does not "
            "promote the master action, does not claim empirical validation, "
            "and does not authorize public readiness. The full ToeFormal "
            "aggregate is recorded as NOT_RUN for this review."
        ),
        "critical_gate_fail_conditions": [
            "treat C_transport^A = 0 as a selected dynamical action term",
            "claim the multiplier/action route is selected",
            "claim the penalty route is licensed",
            "claim direct dynamical-law interpretation is selected",
            "define a norm over the heterogeneous transport tuple without a packet",
            "select Lambda_transport multiplier type or domain",
            "select a component pairing rule",
            "select transport-map domains/codomains",
            "execute C_k or Lambda_transport variation",
            "execute A or metric variation of the candidate",
            "claim transport consistency is proved",
            "claim route-chain compatibility is proved",
            "claim full route alignment is proved",
            "claim any transport component is proved",
            "derive J^nu",
            "derive a psi-current or external-current native route",
            "derive sourced Maxwell",
            "prove matter/current exchange",
            "claim full EM closure",
            "claim QFT-GR closure",
            "claim semiclassical coupling",
            "authorize Phase 2",
            "promote the master action",
            "claim empirical validation or public readiness",
            "record full ToeFormal aggregate as passed, failed, or timed out",
        ],
        "validation_policy": _validation_policy(),
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "aggregate_lean_validation_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativeATransportConsistencyCKFunctionalEmbeddingPacketResultReview",
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
    review.update(_false_boundary_flags())
    return review


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
            "Build the ToE-native A transport-consistency C_k "
            "functional-embedding packet result review."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    review = (
        build_toe_native_a_transport_consistency_ck_functional_embedding_packet_result_review(
            captured_at_utc=args.captured_at_utc
        )
    )
    write_review(review, args.out)


if __name__ == "__main__":
    main()
