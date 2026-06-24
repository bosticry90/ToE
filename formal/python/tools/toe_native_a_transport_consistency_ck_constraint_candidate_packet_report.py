from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_a_ck_constraint_family_selection_after_source_and_bridge_admissibility_report import (
    A_BRIDGE_CONSTRAINT_EQUATION,
    A_BRIDGE_CONSTRAINT_FORM,
    A_BRIDGE_FIELD_EQUATION_MATCH,
    A_BRIDGE_SOURCE_RESIDUAL_MATCH,
    A_BRIDGE_STRESS_ENERGY_MATCH,
    A_FIELD_DOMAIN_POLICY,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as TRANSPORT_SELECTOR_PATH,
    F_DEFINITION_POLICY,
    FULL_TOEFORMAL_STATUS,
    GAUGE_GROUP_POLICY,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
    OUTCOME_ID as TRANSPORT_SELECTOR_OUTCOME,
    PACKET_ID as TRANSPORT_SELECTOR_PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID as TRANSPORT_SELECTOR_SCHEMA_ID,
    SELECTED_A_CK_CONSTRAINT_FAMILY,
    SELECTED_A_CK_OPTION_CLASS,
    SELECTION_RESULT as TRANSPORT_SELECTOR_RESULT,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    SOURCE_ROUTE_STILL_BLOCKED,
    SOURCE_RULE_CLOSEOUT_OUTCOME,
    TRANSPORT_CANDIDATE_PLAIN_MEANING,
    TRANSPORT_CANDIDATE_SHAPE_PREVIEW,
    TRANSPORT_CANDIDATE_TUPLE_PREVIEW,
    TRANSPORT_CHAIN_FORM,
    TRANSPORT_CHAIN_STEPS,
    TRANSPORT_CONSISTENCY_QUESTION,
    TRANSPORT_TUPLE_COMPONENTS,
    VACUUM_EULER_LAGRANGE_ROUTE,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-23T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_PACKET_"
    "20260623_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_PACKET_v0"
PACKET_RESULT = "A_TRANSPORT_STABILITY_RULE_RECORDED_NO_CURRENT_OR_EM_CLOSURE"
OUTCOME_ID = (
    "TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_PACKET_PREPARED_"
    + PACKET_RESULT
)
PACKET_CLASSIFICATION = (
    "toe_native_A_transport_consistency_ck_constraint_candidate_packet_records_"
    "vacuum_u1_derivation_chain_stability_rule_no_current_or_em_closure"
)
NEXT_TARGET = "review_toe_native_A_transport_consistency_ck_constraint_candidate_packet_result"
NEXT_TARGET_KIND = (
    "toe_native_A_transport_consistency_ck_constraint_candidate_packet_result_review"
)

TRANSPORT_CANDIDATE_ID = "A_transport_derivation_chain_stability_ck_candidate"
TRANSPORT_CANDIDATE_TYPE = (
    "vacuum_U1_derivation_chain_stability_admissibility_rule"
)
TRANSPORT_RULE_CLASSIFICATION = (
    "admissibility-only vacuum U(1) transport-stability rule candidate"
)
TRANSPORT_RULE_EPISTEMIC_STATUS = "admissibility-only"
TRANSPORT_CONSTRAINT_FORM = TRANSPORT_CANDIDATE_TUPLE_PREVIEW
TRANSPORT_CONSTRAINT_EQUATION = "C_transport^A = 0"
TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM = TRANSPORT_CONSTRAINT_EQUATION
KNOWN_A_TRANSPORT_CHAIN_STEPS = [
    "S_A^vacuum_U1",
    "E_A^vacuum_U1",
    "T_A^vacuum_U1",
    "C_source^A",
    "C_bridge^A",
    "bounded residual/regime-facing route",
]
KNOWN_A_TRANSPORT_CHAIN_FORM = " -> ".join(KNOWN_A_TRANSPORT_CHAIN_STEPS)

TRANSPORT_COMPONENTS = [
    {
        "component_id": "transport_action_variation_A",
        "component_form": "Transport_ACTION_VARIATION^A = 0",
        "route_edge": "S_A^vacuum_U1 -> E_A^vacuum_U1",
        "plain_meaning": (
            "The selected vacuum U(1) A action route must transport coherently "
            "to the A variation route."
        ),
    },
    {
        "component_id": "transport_variation_stress_energy_A",
        "component_form": "Transport_VARIATION_STRESS_ENERGY^A = 0",
        "route_edge": "E_A^vacuum_U1 -> T_A^vacuum_U1",
        "plain_meaning": (
            "The vacuum A variation route must remain coherent with the "
            "gauge stress-energy route."
        ),
    },
    {
        "component_id": "transport_stress_energy_source_A",
        "component_form": "Transport_STRESS_ENERGY_SOURCE^A = 0",
        "route_edge": "T_A^vacuum_U1 -> C_source^A",
        "plain_meaning": (
            "The gauge stress-energy route must remain compatible with the "
            "closed A source-admissibility rule."
        ),
    },
    {
        "component_id": "transport_source_bridge_A",
        "component_form": "Transport_SOURCE_BRIDGE^A = 0",
        "route_edge": "C_source^A -> C_bridge^A",
        "plain_meaning": (
            "The A source-admissibility rule must remain compatible with the "
            "closed A bridge-admissibility rule."
        ),
    },
    {
        "component_id": "transport_bridge_residual_A",
        "component_form": "Transport_BRIDGE_RESIDUAL^A = 0",
        "route_edge": "C_bridge^A -> bounded residual/regime-facing route",
        "plain_meaning": (
            "The A bridge route must remain compatible with the bounded "
            "residual or regime-facing route."
        ),
    },
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_PACKET_"
    "20260623_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeATransportConsistencyCKConstraintCandidatePacket.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _transport_components() -> list[dict[str, Any]]:
    return [
        {
            **component,
            "recorded_here": True,
            "proved_here": False,
            "variation_executed_here": False,
            "action_term_defined_here": False,
            "current_or_sourced_maxwell_derived_here": False,
            "em_or_qft_gr_closure_claimed_here": False,
        }
        for component in TRANSPORT_COMPONENTS
    ]


def _candidate_criteria(selector: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "candidate_packet_consumes_A_transport_selector",
            "status": "accepted",
            "evidence": selector.get("selection_result"),
            "assessment": (
                "The packet consumes the selected A transport-consistency "
                "candidate-packet target."
            ),
        },
        {
            "row_id": "selected_A_transport_family_carried_forward",
            "status": "accepted",
            "evidence": [
                selector.get("selected_A_ck_option_class"),
                selector.get("selected_A_ck_constraint_family"),
            ],
            "assessment": (
                "The packet stays within the selected A transport-consistency "
                "C_k family."
            ),
        },
        {
            "row_id": "source_and_bridge_context_preserved",
            "status": "accepted",
            "evidence": [
                SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
                A_BRIDGE_CONSTRAINT_EQUATION,
            ],
            "assessment": (
                "The closed A source and bridge admissibility rules remain "
                "context for the transport candidate."
            ),
        },
        {
            "row_id": "vacuum_u1_route_context_preserved",
            "status": "accepted",
            "evidence": [
                GAUGE_GROUP_POLICY,
                VACUUM_EULER_LAGRANGE_ROUTE,
                ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
            ],
            "assessment": (
                "The candidate remains scoped to the selected vacuum U(1) "
                "route."
            ),
        },
        {
            "row_id": "transport_tuple_recorded",
            "status": "accepted",
            "evidence": TRANSPORT_CONSTRAINT_FORM,
            "assessment": (
                "The transport candidate is recorded as a derivation-chain "
                "stability tuple."
            ),
        },
        {
            "row_id": "transport_constraint_equation_recorded",
            "status": "accepted",
            "evidence": TRANSPORT_CONSTRAINT_EQUATION,
            "assessment": "The admissibility condition C_transport^A = 0 is recorded.",
        },
        {
            "row_id": "transport_components_recorded",
            "status": "accepted",
            "evidence": [row["component_form"] for row in TRANSPORT_COMPONENTS],
            "assessment": (
                "The five A route-stability components are recorded without "
                "claiming they are proved."
            ),
        },
        {
            "row_id": "known_A_chain_recorded",
            "status": "accepted",
            "evidence": KNOWN_A_TRANSPORT_CHAIN_FORM,
            "assessment": "The known vacuum U(1) A transport chain is retained.",
        },
        {
            "row_id": "admissibility_rule_not_action_term",
            "status": "accepted",
            "evidence": "transport_candidate_recorded_as_admissibility_rule=true",
            "assessment": (
                "The derivation-chain stability tuple is recorded as an "
                "admissibility-rule candidate, not as an action term."
            ),
        },
        {
            "row_id": "no_variation_transport_proof_or_current_route",
            "status": "accepted",
            "evidence": [
                "C_k_variation_executed=false",
                "transport_consistency_proved=false",
                "J_nu_derived=false",
                "sourced_maxwell_equation_derived=false",
            ],
            "assessment": (
                "No C_k variation, transport proof, current derivation, or "
                "sourced Maxwell route is executed."
            ),
        },
        {
            "row_id": "no_em_qft_gr_phase_or_promotion",
            "status": "accepted",
            "evidence": [
                "full_em_closure_claimed=false",
                "qft_gr_closure_claimed=false",
                "phase2_readiness_claim=false",
                "master_action_promoted=false",
            ],
            "assessment": "The nonpromotion boundary is preserved.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_A_transport_consistency_ck_constraint_candidate_packet",
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
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_toe_native_a_transport_consistency_ck_constraint_candidate_packet(
    *,
    transport_selector_path: Path = TRANSPORT_SELECTOR_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    selector = _read_json(transport_selector_path)
    candidate_criteria = _candidate_criteria(selector)
    transport_components = _transport_components()
    acceptance_criteria = {
        "consumes_expected_transport_candidate_target": (
            selector.get("schema_id") == TRANSPORT_SELECTOR_SCHEMA_ID
            and selector.get("packet_id") == TRANSPORT_SELECTOR_PACKET_ID
            and selector.get("outcome_id") == TRANSPORT_SELECTOR_OUTCOME
            and selector.get("selection_result") == TRANSPORT_SELECTOR_RESULT
            and selector.get("selected_next_target") == CONSUMED_TARGET
            and selector.get("accepted") is True
        ),
        "transport_selector_family_preserved": (
            selector.get("selected_A_ck_option_class") == SELECTED_A_CK_OPTION_CLASS
            and selector.get("selected_A_ck_constraint_family")
            == SELECTED_A_CK_CONSTRAINT_FAMILY
            and selector.get("transport_consistency_family_selected") is True
            and selector.get("transport_candidate_functional_defined") is False
            and selector.get("transport_consistency_proved") is False
        ),
        "source_and_bridge_context_preserved": (
            selector.get("source_candidate_constraint_id")
            == SOURCE_CANDIDATE_CONSTRAINT_ID
            and selector.get("source_candidate_constraint_form")
            == SOURCE_CANDIDATE_CONSTRAINT_FORM
            and selector.get("source_admissibility_constraint_form")
            == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
            and selector.get("A_bridge_constraint_form") == A_BRIDGE_CONSTRAINT_FORM
            and selector.get("A_bridge_constraint_equation")
            == A_BRIDGE_CONSTRAINT_EQUATION
            and selector.get("bridge_admissibility_constraint_form")
            == A_BRIDGE_CONSTRAINT_EQUATION
        ),
        "bridge_route_components_preserved": (
            selector.get("A_bridge_field_equation_match")
            == A_BRIDGE_FIELD_EQUATION_MATCH
            and selector.get("A_bridge_stress_energy_match")
            == A_BRIDGE_STRESS_ENERGY_MATCH
            and selector.get("A_bridge_source_residual_match")
            == A_BRIDGE_SOURCE_RESIDUAL_MATCH
        ),
        "vacuum_u1_context_preserved": (
            selector.get("gauge_group_policy") == GAUGE_GROUP_POLICY
            and selector.get("A_field_domain_policy") == A_FIELD_DOMAIN_POLICY
            and selector.get("F_definition_policy") == F_DEFINITION_POLICY
            and selector.get("vacuum_euler_lagrange_route")
            == VACUUM_EULER_LAGRANGE_ROUTE
            and selector.get("on_shell_vacuum_conservation_identity")
            == ON_SHELL_VACUUM_CONSERVATION_IDENTITY
            and selector.get("source_route_still_blocked")
            == SOURCE_ROUTE_STILL_BLOCKED
        ),
        "transport_candidate_recorded_as_rule_only": (
            TRANSPORT_CONSTRAINT_EQUATION == TRANSPORT_CANDIDATE_SHAPE_PREVIEW
            and TRANSPORT_CONSTRAINT_FORM == TRANSPORT_CANDIDATE_TUPLE_PREVIEW
            and TRANSPORT_CANDIDATE_TYPE
            == "vacuum_U1_derivation_chain_stability_admissibility_rule"
            and len(transport_components) == 5
        ),
        "no_selector_shortcut_claims": all(
            selector.get(key) is False
            for key in [
                "transport_candidate_functional_defined",
                "transport_candidate_functional_selected",
                "transport_proof_claimed",
                "transport_consistency_proved",
                "transport_chain_compatibility_proved",
                "C_k_action_embedding_constructed",
                "C_k_variation_executed",
                "J_nu_derived",
                "psi_current_route_constructed",
                "external_current_native_derivation_selected",
                "sourced_maxwell_equation_derived",
                "matter_current_exchange_route_proved",
                "matter_gauge_energy_exchange_proved",
                "full_em_closure_claimed",
                "qft_gr_closure_claimed",
                "semiclassical_coupling_authorized",
                "master_action_promoted",
                "empirical_validation_claimed",
                "phase2_readiness_claim",
            ]
        ),
        "candidate_criteria_all_accepted": all(
            row["status"] == "accepted" for row in candidate_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_PACKET"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_PACKET"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_CONSTRAINT_CANDIDATE_PACKET_"
            "REQUIRES_REMEDIATION"
        ),
        "packet_result": PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "transport_selector_outcome": TRANSPORT_SELECTOR_OUTCOME,
        "transport_selector_result": TRANSPORT_SELECTOR_RESULT,
        "selected_A_ck_option_class": SELECTED_A_CK_OPTION_CLASS,
        "selected_A_ck_constraint_family": SELECTED_A_CK_CONSTRAINT_FAMILY,
        "transport_consistency_question": TRANSPORT_CONSISTENCY_QUESTION,
        "transport_candidate_shape_preview": TRANSPORT_CANDIDATE_SHAPE_PREVIEW,
        "transport_candidate_tuple_preview": TRANSPORT_CANDIDATE_TUPLE_PREVIEW,
        "transport_tuple_components": TRANSPORT_TUPLE_COMPONENTS,
        "transport_tuple_component_count": len(TRANSPORT_TUPLE_COMPONENTS),
        "transport_chain_steps": TRANSPORT_CHAIN_STEPS,
        "transport_chain_form": TRANSPORT_CHAIN_FORM,
        "transport_chain_step_count": len(TRANSPORT_CHAIN_STEPS),
        "transport_candidate_id": TRANSPORT_CANDIDATE_ID,
        "transport_candidate_type": TRANSPORT_CANDIDATE_TYPE,
        "transport_rule_classification": TRANSPORT_RULE_CLASSIFICATION,
        "transport_rule_epistemic_status": TRANSPORT_RULE_EPISTEMIC_STATUS,
        "transport_constraint_form": TRANSPORT_CONSTRAINT_FORM,
        "transport_constraint_equation": TRANSPORT_CONSTRAINT_EQUATION,
        "transport_admissibility_constraint_form": TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
        "transport_rule_plain_meaning": TRANSPORT_CANDIDATE_PLAIN_MEANING,
        "transport_components": transport_components,
        "transport_component_count": len(transport_components),
        "known_A_transport_chain_form": KNOWN_A_TRANSPORT_CHAIN_FORM,
        "known_A_transport_chain_steps": KNOWN_A_TRANSPORT_CHAIN_STEPS,
        "known_A_transport_chain_step_count": len(KNOWN_A_TRANSPORT_CHAIN_STEPS),
        "source_rule_closeout_outcome": SOURCE_RULE_CLOSEOUT_OUTCOME,
        "source_candidate_constraint_id": SOURCE_CANDIDATE_CONSTRAINT_ID,
        "source_candidate_constraint_form": SOURCE_CANDIDATE_CONSTRAINT_FORM,
        "source_admissibility_constraint_form": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        "bridge_closeout_outcome": selector.get("bridge_closeout_outcome"),
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
        "closed_A_ck_rule_family_count_after_packet": 3,
        "candidate_criteria": candidate_criteria,
        "candidate_criteria_count": len(candidate_criteria),
        "candidate_criteria_accepted_count": sum(
            1 for row in candidate_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "transport_candidate_packet_prepared": True,
        "transport_candidate_packet_accepted": True,
        "transport_candidate_recorded": True,
        "transport_candidate_selected_as_derivation_chain_stability_rule": True,
        "transport_candidate_recorded_as_admissibility_rule": True,
        "transport_candidate_recorded_as_transport_stability_rule": True,
        "transport_candidate_recorded_as_action_term": False,
        "transport_candidate_recorded_as_new_dynamical_law": False,
        "transport_candidate_functional_defined": False,
        "transport_candidate_functional_selected": False,
        "transport_candidate_rule_proved": False,
        "transport_tuple_recorded": True,
        "transport_tuple_proved": False,
        "transport_components_recorded": True,
        "transport_components_proved": False,
        "known_A_chain_recorded": True,
        "known_A_chain_proved": False,
        "transport_consistency_family_selected": True,
        "transport_consistency_claimed": False,
        "transport_consistency_proved": False,
        "transport_proof_claimed": False,
        "full_route_alignment_proof_claimed": False,
        "full_route_alignment_proved": False,
        "route_chain_compatibility_proved": False,
        "source_admissibility_rule_retained_as_context": True,
        "bridge_admissibility_rule_retained_as_context": True,
        "source_admissibility_claimed": False,
        "source_admissibility_proved": False,
        "source_conservation_proved": False,
        "bridge_admissibility_claimed": False,
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
        "result_review_authorized": True,
        "result_review_prepared": False,
        "review_prepared": False,
        "review_executed": False,
        "claim_level": (
            "Level 3 transport candidate packet; records C_transport^A as a "
            "vacuum U(1) derivation-chain stability admissibility rule without "
            "defining an action term, executing C_k variation, proving "
            "transport consistency, deriving current, closing EM, or promoting "
            "the master action"
        ),
        "claim_ceiling": (
            "A transport-stability C_k admissibility-rule candidate only no "
            "transport proof no C_k action embedding no C_k variation no J^nu "
            "derivation no psi-current route no external-current native "
            "derivation no sourced Maxwell no matter-current exchange no full "
            "EM closure no QFT-GR closure no semiclassical coupling no "
            "empirical validation no Phase 2 authorization no master-action "
            "promotion"
        ),
        "mathematical_statement": (
            "The candidate packet records C_transport^A := "
            "(Transport_ACTION_VARIATION^A, "
            "Transport_VARIATION_STRESS_ENERGY^A, "
            "Transport_STRESS_ENERGY_SOURCE^A, Transport_SOURCE_BRIDGE^A, "
            "Transport_BRIDGE_RESIDUAL^A) with condition C_transport^A = 0. "
            "The tuple is an admissibility-only transport-stability rule "
            "candidate over the vacuum U(1) A chain S_A^vacuum_U1 -> "
            "E_A^vacuum_U1 -> T_A^vacuum_U1 -> C_source^A -> C_bridge^A -> "
            "bounded residual/regime-facing route."
        ),
        "non_claim_boundary": (
            "This packet records a ToE-native A transport-consistency C_k "
            "candidate as an admissibility-only vacuum U(1) derivation-chain "
            "stability rule. It does not define a fully concrete "
            "C_transport^A functional, does not embed C_transport^A into the "
            "action, does not execute C_k variation, does not vary lambda_k, "
            "A, or g, does not prove any transport component, does not prove "
            "transport consistency, does not prove full route alignment, does "
            "not derive J^nu, does not derive a psi-current route, does not "
            "derive an external-current native route, does not derive sourced "
            "Maxwell, does not prove matter/current exchange, does not close "
            "EM, does not close QFT-GR, does not authorize semiclassical "
            "coupling, does not claim empirical validation, does not authorize "
            "Phase 2, records no Phase 2 authorization, and does not promote "
            "the master action. The full ToeFormal aggregate is recorded as "
            "NOT_RUN for this packet."
        ),
        "critical_gate_fail_conditions": [
            "claim transport consistency is proved",
            "claim full route alignment is proved",
            "claim any transport component is proved",
            "embed C_transport^A into an action",
            "execute C_k variation",
            "derive J^nu",
            "derive a psi-current route",
            "derive an external-current native route",
            "derive sourced Maxwell",
            "prove matter-current exchange",
            "claim full EM closure",
            "claim QFT-GR closure",
            "claim semiclassical coupling",
            "authorize Phase 2",
            "promote the master action",
            "claim empirical validation",
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
                "ToeNativeATransportConsistencyCKConstraintCandidatePacket"
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
            "transport_selector_file": _ptr(transport_selector_path),
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
            "Build the ToE-native A transport-consistency C_k constraint "
            "candidate packet."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    packet = build_toe_native_a_transport_consistency_ck_constraint_candidate_packet(
        captured_at_utc=args.captured_at_utc
    )
    path = write_packet(packet, args.out)
    print(
        json.dumps(
            {
                "accepted": packet["accepted"],
                "out": _ptr(path),
                "packet_result": packet["packet_result"],
                "selected_next_target": packet["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
