from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_a_transport_consistency_ck_constraint_candidate_packet_report import (
    A_BRIDGE_CONSTRAINT_EQUATION,
    A_BRIDGE_CONSTRAINT_FORM,
    A_BRIDGE_FIELD_EQUATION_MATCH,
    A_BRIDGE_SOURCE_RESIDUAL_MATCH,
    A_BRIDGE_STRESS_ENERGY_MATCH,
    A_FIELD_DOMAIN_POLICY,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as CANDIDATE_PACKET_PATH,
    F_DEFINITION_POLICY,
    FULL_TOEFORMAL_STATUS,
    GAUGE_GROUP_POLICY,
    KNOWN_A_TRANSPORT_CHAIN_FORM,
    KNOWN_A_TRANSPORT_CHAIN_STEPS,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
    OUTCOME_ID as CANDIDATE_PACKET_OUTCOME,
    PACKET_ID as CANDIDATE_PACKET_ID,
    PACKET_RESULT as CANDIDATE_PACKET_RESULT,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID as CANDIDATE_PACKET_SCHEMA_ID,
    SELECTED_A_CK_CONSTRAINT_FAMILY,
    SELECTED_A_CK_OPTION_CLASS,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    SOURCE_ROUTE_STILL_BLOCKED,
    SOURCE_RULE_CLOSEOUT_OUTCOME,
    TRANSPORT_CANDIDATE_ID,
    TRANSPORT_CANDIDATE_TYPE,
    TRANSPORT_COMPONENTS,
    TRANSPORT_CONSTRAINT_EQUATION,
    TRANSPORT_CONSTRAINT_FORM,
    TRANSPORT_RULE_CLASSIFICATION,
    TRANSPORT_RULE_EPISTEMIC_STATUS,
    VACUUM_EULER_LAGRANGE_ROUTE,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-23T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_PACKET_"
    "RESULT_REVIEW_20260623_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_PACKET_"
    "RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_RESULT_REVIEW_"
    "ACCEPTS_VACUUM_U1_DERIVATION_CHAIN_STABILITY_CANDIDATE_"
    "NO_FUNCTIONALIZATION_OR_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_RESULT = "REVIEW_ACCEPTED"
PACKET_CLASSIFICATION = (
    "toe_native_A_transport_consistency_ck_constraint_candidate_result_review_"
    "accepts_vacuum_u1_derivation_chain_stability_candidate_"
    "no_functionalization_or_promotion"
)
NEXT_TARGET = "prepare_toe_native_A_transport_consistency_ck_functional_embedding_packet"
NEXT_TARGET_KIND = (
    "toe_native_A_transport_consistency_ck_functional_embedding_packet_preparation"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_PACKET_"
    "RESULT_REVIEW_20260623_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeATransportConsistencyCKConstraintCandidatePacketResultReview.lean"
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
            "row_id": "transport_candidate_review_target_consumed",
            "status": "accepted",
            "evidence": packet.get("selected_next_target"),
            "assessment": "The active A transport candidate result-review target is consumed.",
        },
        {
            "row_id": "C_transport_A_tuple_preserved_exactly",
            "status": "accepted",
            "evidence": TRANSPORT_CONSTRAINT_FORM,
            "assessment": "The A transport derivation-chain stability tuple is preserved exactly.",
        },
        {
            "row_id": "C_transport_A_equation_preserved_exactly",
            "status": "accepted",
            "evidence": TRANSPORT_CONSTRAINT_EQUATION,
            "assessment": "The condition C_transport^A = 0 is preserved.",
        },
        {
            "row_id": "transport_components_preserved_unproved",
            "status": "accepted",
            "evidence": [row["component_form"] for row in TRANSPORT_COMPONENTS],
            "assessment": "The transport components are retained without proving any component.",
        },
        {
            "row_id": "vacuum_u1_scope_preserved",
            "status": "accepted",
            "evidence": [
                GAUGE_GROUP_POLICY,
                A_FIELD_DOMAIN_POLICY,
                F_DEFINITION_POLICY,
                VACUUM_EULER_LAGRANGE_ROUTE,
            ],
            "assessment": "The candidate remains scoped to the selected vacuum U(1) route.",
        },
        {
            "row_id": "source_and_bridge_rules_retained_as_context",
            "status": "accepted",
            "evidence": [
                SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
                A_BRIDGE_CONSTRAINT_EQUATION,
            ],
            "assessment": "The closed A source and bridge rules remain context.",
        },
        {
            "row_id": "known_A_chain_retained",
            "status": "accepted",
            "evidence": KNOWN_A_TRANSPORT_CHAIN_FORM,
            "assessment": "The known vacuum U(1) A route chain remains the grounding chain.",
        },
        {
            "row_id": "admissibility_only_classification_preserved",
            "status": "accepted",
            "evidence": TRANSPORT_RULE_CLASSIFICATION,
            "assessment": "The transport rule remains an admissibility-only candidate.",
        },
        {
            "row_id": "no_transport_proof_or_concrete_functional",
            "status": "accepted",
            "evidence": [
                "transport_consistency_proved=false",
                "transport_candidate_functional_defined=false",
            ],
            "assessment": "No transport proof or concrete C_transport^A functional is claimed.",
        },
        {
            "row_id": "no_ck_action_embedding_or_variation",
            "status": "accepted",
            "evidence": [
                "C_k_action_embedding_constructed=false",
                "candidate_action_insertion_executed=false",
                "C_k_variation_executed=false",
            ],
            "assessment": "No C_k action embedding or variation is executed.",
        },
        {
            "row_id": "no_current_sourced_maxwell_or_exchange_route",
            "status": "accepted",
            "evidence": [
                "J_nu_derived=false",
                "psi_current_route_constructed=false",
                "external_current_native_derivation_selected=false",
                "sourced_maxwell_equation_derived=false",
                "matter_current_exchange_route_proved=false",
            ],
            "assessment": "No current, sourced Maxwell, or exchange route is introduced.",
        },
        {
            "row_id": "no_closure_coupling_validation_phase_or_promotion",
            "status": "accepted",
            "evidence": [
                "full_em_closure_claimed=false",
                "qft_gr_closure_claimed=false",
                "semiclassical_coupling_authorized=false",
                "empirical_validation_claimed=false",
                "phase2_readiness_claim=false",
                "master_action_promoted=false",
            ],
            "assessment": "No closure, coupling, validation, Phase 2, or promotion follows.",
        },
        {
            "row_id": "full_toeformal_aggregate_recorded_not_run",
            "status": "accepted",
            "evidence": FULL_TOEFORMAL_STATUS,
            "assessment": "The full ToeFormal aggregate remains recorded as NOT_RUN.",
        },
        {
            "row_id": "functional_embedding_packet_selected",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": (
                "The next bounded packet may test and likely block action "
                "embedding routes for C_transport^A."
            ),
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "toe_native_A_transport_consistency_ck_constraint_candidate_packet_"
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
        "toeformal_import_update_requires_preservation_status": True,
        "aggregate_lean_validation_status_for_packet": FULL_TOEFORMAL_STATUS,
        "aggregate_lean_validation_status_allowed_values": ["NOT_RUN"],
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


def build_toe_native_a_transport_consistency_ck_constraint_candidate_packet_result_review(
    *,
    candidate_packet_path: Path = CANDIDATE_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(candidate_packet_path)
    criteria = _review_criteria(packet)
    acceptance_criteria = {
        "consumes_expected_review_target": (
            packet.get("schema_id") == CANDIDATE_PACKET_SCHEMA_ID
            and packet.get("packet_id") == CANDIDATE_PACKET_ID
            and packet.get("outcome_id") == CANDIDATE_PACKET_OUTCOME
            and packet.get("packet_result") == CANDIDATE_PACKET_RESULT
            and packet.get("selected_next_target") == CONSUMED_TARGET
            and packet.get("accepted") is True
        ),
        "transport_candidate_exact": (
            packet.get("transport_candidate_id") == TRANSPORT_CANDIDATE_ID
            and packet.get("transport_candidate_type") == TRANSPORT_CANDIDATE_TYPE
            and packet.get("transport_rule_classification")
            == TRANSPORT_RULE_CLASSIFICATION
            and packet.get("transport_rule_epistemic_status")
            == TRANSPORT_RULE_EPISTEMIC_STATUS
            and packet.get("transport_constraint_form") == TRANSPORT_CONSTRAINT_FORM
            and packet.get("transport_constraint_equation")
            == TRANSPORT_CONSTRAINT_EQUATION
        ),
        "transport_components_exact_unproved": (
            packet.get("transport_component_count") == len(TRANSPORT_COMPONENTS)
            and packet.get("transport_components_recorded") is True
            and packet.get("transport_components_proved") is False
            and [
                row.get("component_form")
                for row in packet.get("transport_components", [])
            ]
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
        "bridge_route_context_exact": (
            packet.get("A_bridge_field_equation_match")
            == A_BRIDGE_FIELD_EQUATION_MATCH
            and packet.get("A_bridge_stress_energy_match")
            == A_BRIDGE_STRESS_ENERGY_MATCH
            and packet.get("A_bridge_source_residual_match")
            == A_BRIDGE_SOURCE_RESIDUAL_MATCH
        ),
        "vacuum_u1_scope_preserved": (
            packet.get("gauge_group_policy") == GAUGE_GROUP_POLICY
            and packet.get("A_field_domain_policy") == A_FIELD_DOMAIN_POLICY
            and packet.get("F_definition_policy") == F_DEFINITION_POLICY
            and packet.get("vacuum_euler_lagrange_route")
            == VACUUM_EULER_LAGRANGE_ROUTE
            and packet.get("on_shell_vacuum_conservation_identity")
            == ON_SHELL_VACUUM_CONSERVATION_IDENTITY
            and packet.get("source_route_still_blocked")
            == SOURCE_ROUTE_STILL_BLOCKED
        ),
        "known_chain_exact": (
            packet.get("known_A_transport_chain_form")
            == KNOWN_A_TRANSPORT_CHAIN_FORM
            and packet.get("known_A_transport_chain_steps")
            == KNOWN_A_TRANSPORT_CHAIN_STEPS
            and packet.get("known_A_chain_recorded") is True
            and packet.get("known_A_chain_proved") is False
        ),
        "candidate_only_boundary_carried_forward": (
            packet.get("transport_candidate_recorded_as_admissibility_rule") is True
            and packet.get("transport_candidate_recorded_as_action_term") is False
            and packet.get("transport_candidate_recorded_as_new_dynamical_law")
            is False
            and packet.get("transport_candidate_rule_proved") is False
            and packet.get("transport_tuple_proved") is False
            and packet.get("transport_consistency_proved") is False
            and packet.get("full_route_alignment_proved") is False
        ),
        "no_functionalization_variation_current_closure_or_promotion": all(
            packet.get(key) is False
            for key in [
                "transport_candidate_functional_defined",
                "transport_candidate_functional_selected",
                "concrete_ck_functional_selected",
                "concrete_ck_functional_defined",
                "fully_concrete_ck_functional_selected",
                "fully_concrete_ck_functional_defined",
                "ck_action_embedding_claimed",
                "ck_action_embedding_constructed",
                "C_k_action_embedding_constructed",
                "candidate_action_insertion_executed",
                "constraint_as_action_term_selected",
                "constraint_term_selected",
                "ck_variation_executed",
                "C_k_variation_executed",
                "lambda_variation_executed",
                "metric_variation_of_candidate_executed",
                "A_variation_of_candidate_executed",
                "J_nu_derived",
                "psi_current_route_constructed",
                "external_current_native_derivation_selected",
                "sourced_maxwell_equation_derived",
                "sourced_maxwell_route_derived",
                "matter_current_exchange_route_proved",
                "matter_gauge_energy_exchange_proved",
                "full_em_closure_claimed",
                "qft_gr_closure_claimed",
                "semiclassical_coupling_authorized",
                "master_action_promoted",
                "canonical_master_action_promoted",
                "empirical_validation_claimed",
                "phase2_readiness_claim",
            ]
        ),
        "aggregate_recorded_not_run": (
            packet.get("full_toeformal_aggregate_status_for_packet")
            == FULL_TOEFORMAL_STATUS
            and packet.get("aggregate_lean_validation_status_for_packet")
            == FULL_TOEFORMAL_STATUS
            and packet.get("full_toeformal_aggregate_passed") is False
            and packet.get("full_toeformal_aggregate_failed") is False
            and packet.get("full_toeformal_aggregate_timed_out") is False
        ),
        "criteria_all_accepted": all(row["status"] == "accepted" for row in criteria),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_CANDIDATE_REVIEW"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_"
            "CANDIDATE_PACKET_RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_CANDIDATE_REVIEW_REQUIRES_REMEDIATION",
        "packet_result": PACKET_RESULT,
        "review_result": REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "candidate_packet_outcome": CANDIDATE_PACKET_OUTCOME,
        "candidate_packet_result": CANDIDATE_PACKET_RESULT,
        "selected_A_ck_option_class": SELECTED_A_CK_OPTION_CLASS,
        "selected_A_ck_constraint_family": SELECTED_A_CK_CONSTRAINT_FAMILY,
        "transport_candidate_id": TRANSPORT_CANDIDATE_ID,
        "transport_candidate_type": TRANSPORT_CANDIDATE_TYPE,
        "transport_rule_classification": TRANSPORT_RULE_CLASSIFICATION,
        "transport_rule_epistemic_status": TRANSPORT_RULE_EPISTEMIC_STATUS,
        "transport_constraint_form": TRANSPORT_CONSTRAINT_FORM,
        "transport_constraint_equation": TRANSPORT_CONSTRAINT_EQUATION,
        "transport_admissibility_constraint_form": TRANSPORT_CONSTRAINT_EQUATION,
        "transport_component_count": len(TRANSPORT_COMPONENTS),
        "transport_component_forms": [
            row["component_form"] for row in TRANSPORT_COMPONENTS
        ],
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
        "closed_A_ck_rule_family_count_after_review": 3,
        "review_accepts_vacuum_u1_derivation_chain_stability_candidate": True,
        "derivation_chain_stability_candidate_accepted": True,
        "transport_constraint_preserved": True,
        "transport_tuple_preserved": True,
        "transport_components_preserved": True,
        "transport_components_proved": False,
        "transport_candidate_classified_as_admissibility_only": True,
        "source_and_bridge_context_retained": True,
        "vacuum_u1_scope_preserved": True,
        "known_A_chain_retained": True,
        "functional_embedding_packet_authorized": True,
        "functional_embedding_packet_prepared": False,
        "functional_embedding_executed": False,
        "multiplier_action_route_test_authorized": True,
        "penalty_route_test_authorized": True,
        "direct_dynamical_law_interpretation_test_authorized": True,
        "multiplier_action_route_selected": False,
        "penalty_route_selected": False,
        "direct_dynamical_law_interpretation_selected": False,
        "transport_candidate_functional_defined": False,
        "transport_candidate_functional_selected": False,
        "transport_candidate_recorded_as_action_term": False,
        "transport_candidate_recorded_as_new_dynamical_law": False,
        "transport_candidate_rule_proved": False,
        "transport_consistency_claimed": False,
        "transport_consistency_proved": False,
        "transport_proof_claimed": False,
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
        "concrete_ck_functional_selected": False,
        "concrete_ck_functional_defined": False,
        "fully_concrete_ck_functional_selected": False,
        "fully_concrete_ck_functional_defined": False,
        "ck_action_embedding_claimed": False,
        "ck_action_embedding_selected": False,
        "ck_action_embedding_constructed": False,
        "C_k_action_embedding_selected": False,
        "C_k_action_embedding_constructed": False,
        "candidate_action_insertion_executed": False,
        "constraint_as_action_term_selected": False,
        "constraint_term_selected": False,
        "ck_variation_executed": False,
        "ck_variation_authorized": False,
        "C_k_variation_executed": False,
        "C_k_variation_authorized": False,
        "lambda_variation_executed": False,
        "metric_variation_of_candidate_executed": False,
        "A_variation_of_candidate_executed": False,
        "metric_variation_executed": False,
        "A_variation_executed": False,
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
        "review_criteria": criteria,
        "review_criteria_count": len(criteria),
        "review_criteria_accepted_count": sum(
            1 for row in criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "proof_depth_label": (
            "A_TRANSPORT_CONSISTENCY_CK_CANDIDATE_REVIEW_ACCEPTED_"
            "NO_FUNCTIONALIZATION"
        ),
        "mathematical_statement": (
            "The review accepts the ToE-native A transport-consistency C_k "
            "candidate as an admissibility-only vacuum U(1) derivation-chain "
            "stability rule candidate: "
            + TRANSPORT_CONSTRAINT_FORM
            + ", with condition "
            + TRANSPORT_CONSTRAINT_EQUATION
            + ". The source and bridge rules remain context; no transport "
            "proof, action embedding, current derivation, EM closure, or "
            "promotion is claimed."
        ),
        "non_claim_boundary": (
            "This review accepts C_transport^A = 0 only as an "
            "admissibility-only vacuum U(1) derivation-chain stability "
            "candidate. It does not define a fully concrete C_transport^A "
            "functional, does not functionalize C_transport^A, does not embed "
            "C_transport^A into the action, does not define a C_k action term, "
            "does not select a multiplier/action route, does not select a "
            "penalty route, does not interpret the candidate as a direct "
            "dynamical law, does not execute C_k variation, does not vary "
            "lambda_k, A, or g, does not prove any transport component, does "
            "not prove transport consistency, does not prove full route "
            "alignment, does not prove source admissibility, does not prove "
            "bridge admissibility, does not derive J^nu, does not derive a "
            "psi-current route, does not derive an external-current native "
            "route, does not derive sourced Maxwell, does not prove "
            "matter/current exchange, does not close EM, does not close "
            "QFT-GR, does not authorize semiclassical coupling, does not "
            "claim empirical validation, does not authorize Phase 2, records "
            "no Phase 2 authorization, does not promote the master action, "
            "and does not authorize public readiness. The full ToeFormal "
            "aggregate is recorded as NOT_RUN for this review."
        ),
        "critical_gate_fail_conditions": [
            "functionalize or embed C_transport^A as an action term",
            "select a multiplier/action route",
            "select a penalty route",
            "interpret C_transport^A as a direct dynamical law",
            "execute C_k or lambda variation",
            "execute A or metric variation of the transport candidate",
            "claim transport consistency is proved",
            "claim full route alignment is proved",
            "claim any transport component is proved",
            "derive J^nu",
            "derive a psi-current route",
            "derive an external-current native route",
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
        "aggregate_lean_validation_status_for_packet": FULL_TOEFORMAL_STATUS,
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "lane_level_lean_targets": [
            (
                "ToeFormal.Derivation."
                "ToeNativeATransportConsistencyCKConstraintCandidatePacketResultReview"
            ),
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
            "candidate_packet_file": _ptr(candidate_packet_path),
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
            "Build the ToE-native A transport-consistency C_k constraint "
            "candidate packet result review."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    review = (
        build_toe_native_a_transport_consistency_ck_constraint_candidate_packet_result_review(
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
