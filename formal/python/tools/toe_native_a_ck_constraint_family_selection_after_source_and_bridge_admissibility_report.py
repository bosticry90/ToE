from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

sys.setrecursionlimit(10000)

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_a_bridge_admissibility_ck_admissibility_rule_closeout_report import (
    A_BRIDGE_CANDIDATE_ID,
    A_BRIDGE_CONSTRAINT_EQUATION,
    A_BRIDGE_CONSTRAINT_FORM,
    A_BRIDGE_FIELD_EQUATION_MATCH,
    A_BRIDGE_SOURCE_RESIDUAL_MATCH,
    A_BRIDGE_STRESS_ENERGY_MATCH,
    A_FIELD_DOMAIN_POLICY,
    BRIDGE_RULE_EPISTEMIC_STATUS,
    CLOSEOUT_RESULT as BRIDGE_CLOSEOUT_RESULT,
    CURRENT_TARGET_AGGREGATE_PATH,
    DEFAULT_OUT as BRIDGE_CLOSEOUT_PATH,
    F_DEFINITION_POLICY,
    FULL_TOEFORMAL_STATUS,
    GAUGE_GROUP_POLICY,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    NEXT_RECOMMENDED_A_CK_CANDIDATE_TARGET,
    NEXT_RECOMMENDED_A_CK_FAMILY,
    NEXT_TARGET as CONSUMED_TARGET,
    ON_SHELL_VACUUM_CONSERVATION_IDENTITY,
    OUTCOME_ID as BRIDGE_CLOSEOUT_OUTCOME,
    PACKET_ID as BRIDGE_CLOSEOUT_PACKET_ID,
    QFTGR_AGGREGATE_PATH,
    RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH,
    SCHEMA_ID as BRIDGE_CLOSEOUT_SCHEMA_ID,
    SELECTED_A_CK_CONSTRAINT_FAMILY as BRIDGE_SELECTED_A_CK_CONSTRAINT_FAMILY,
    SELECTED_A_CK_OPTION_CLASS as BRIDGE_SELECTED_A_CK_OPTION_CLASS,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    SOURCE_ROUTE_STILL_BLOCKED,
    SOURCE_RULE_CLOSEOUT_OUTCOME,
    VACUUM_EULER_LAGRANGE_ROUTE,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-23T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_A_CK_CONSTRAINT_FAMILY_SELECTION_AFTER_SOURCE_AND_BRIDGE_"
    "ADMISSIBILITY_20260623_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "TOE_NATIVE_A_CK_CONSTRAINT_FAMILY_SELECTION_AFTER_SOURCE_AND_BRIDGE_"
    "ADMISSIBILITY_v0"
)
SELECTION_RESULT = (
    "TOE_NATIVE_A_CK_CONSTRAINT_FAMILY_SELECTION_AFTER_SOURCE_AND_BRIDGE_"
    "ADMISSIBILITY_SELECTS_TRANSPORT_CONSISTENCY_NO_CURRENT_OR_EM_CLOSURE"
)
OUTCOME_ID = SELECTION_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_A_ck_constraint_family_selection_after_source_and_bridge_"
    "admissibility_selects_transport_consistency_no_current_or_em_closure"
)
NEXT_TARGET = "prepare_toe_native_A_transport_consistency_ck_constraint_candidate_packet"
NEXT_TARGET_KIND = (
    "toe_native_A_transport_consistency_ck_constraint_candidate_packet_preparation"
)

SELECTED_A_CK_OPTION_CLASS = "transport_consistency_constraint"
SELECTED_A_CK_CONSTRAINT_FAMILY = "A_transport_consistency_constraint_family"
SELECTED_FAMILY_SELECTION_STATUS = (
    "selected_as_next_A_ck_family_after_source_and_bridge_admissibility"
)

SOURCE_RULE_MEANING = (
    "the vacuum gauge stress-energy route may source gravity only if conserved"
)
BRIDGE_RULE_MEANING = (
    "the master-action A route must match the selected vacuum U(1) route"
)
TRANSPORT_CONSISTENCY_QUESTION = (
    "Does the vacuum U(1) A route remain coherent through the derivation chain?"
)
TRANSPORT_CANDIDATE_SHAPE_PREVIEW = "C_transport^A = 0"
TRANSPORT_CANDIDATE_TUPLE_PREVIEW = (
    "C_transport^A := (Transport_ACTION_VARIATION^A, "
    "Transport_VARIATION_STRESS_ENERGY^A, "
    "Transport_STRESS_ENERGY_SOURCE^A, "
    "Transport_SOURCE_BRIDGE^A, Transport_BRIDGE_RESIDUAL^A)"
)
TRANSPORT_TUPLE_COMPONENTS = [
    "Transport_ACTION_VARIATION^A",
    "Transport_VARIATION_STRESS_ENERGY^A",
    "Transport_STRESS_ENERGY_SOURCE^A",
    "Transport_SOURCE_BRIDGE^A",
    "Transport_BRIDGE_RESIDUAL^A",
]
TRANSPORT_CANDIDATE_PLAIN_MEANING = (
    "The vacuum U(1) A route is admitted only if its field equation, "
    "stress-energy route, source rule, and bridge rule remain coherent "
    "through the derivation chain."
)
TRANSPORT_CHAIN_STEPS = [
    "ACTION_VARIATION",
    "VARIATION_STRESS_ENERGY",
    "STRESS_ENERGY_SOURCE",
    "SOURCE_BRIDGE",
    "BRIDGE_RESIDUAL",
]
TRANSPORT_CHAIN_FORM = " -> ".join(TRANSPORT_CHAIN_STEPS)

A_CURRENT_OR_SOURCED_EM_CONSTRAINT_FAMILY = (
    "A_current_or_sourced_EM_constraint_family"
)
A_CURRENT_OR_SOURCED_EM_FAMILY_STATUS = (
    "blocked_pending_J_nu_psi_current_external_current_sourced_maxwell_and_exchange"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_A_CK_CONSTRAINT_FAMILY_SELECTION_AFTER_SOURCE_AND_BRIDGE_"
    "ADMISSIBILITY_20260623_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeACKConstraintFamilySelectionAfterSourceAndBridgeAdmissibility.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _candidate_family_options() -> list[dict[str, Any]]:
    return [
        {
            "constraint_option_class": "source_admissibility_constraint",
            "constraint_family_id": "A_source_admissibility_constraint_family",
            "selection_status": "closed_as_retained_context_not_reselected",
            "candidate_shape": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
            "plain_meaning": SOURCE_RULE_MEANING,
            "candidate_packet_target": None,
            "concrete_functional_defined": False,
            "ck_variation_executed": False,
            "current_or_em_closure_claimed": False,
        },
        {
            "constraint_option_class": "bridge_admissibility_constraint",
            "constraint_family_id": BRIDGE_SELECTED_A_CK_CONSTRAINT_FAMILY,
            "selection_status": "closed_as_retained_context_not_reselected",
            "candidate_shape": A_BRIDGE_CONSTRAINT_EQUATION,
            "plain_meaning": BRIDGE_RULE_MEANING,
            "candidate_packet_target": None,
            "concrete_functional_defined": False,
            "ck_variation_executed": False,
            "current_or_em_closure_claimed": False,
        },
        {
            "constraint_option_class": SELECTED_A_CK_OPTION_CLASS,
            "constraint_family_id": SELECTED_A_CK_CONSTRAINT_FAMILY,
            "selection_status": SELECTED_FAMILY_SELECTION_STATUS,
            "candidate_packet_target": NEXT_TARGET,
            "recommended_candidate_shape_preview": TRANSPORT_CANDIDATE_SHAPE_PREVIEW,
            "recommended_candidate_tuple_preview": TRANSPORT_CANDIDATE_TUPLE_PREVIEW,
            "concrete_functional_defined": False,
            "transport_consistency_proved": False,
            "ck_variation_executed": False,
            "current_or_em_closure_claimed": False,
        },
        {
            "constraint_option_class": "current_or_sourced_EM_constraint",
            "constraint_family_id": A_CURRENT_OR_SOURCED_EM_CONSTRAINT_FAMILY,
            "selection_status": A_CURRENT_OR_SOURCED_EM_FAMILY_STATUS,
            "candidate_packet_target": None,
            "J_nu_derived": False,
            "psi_current_route_constructed": False,
            "external_current_native_derivation_selected": False,
            "sourced_maxwell_equation_derived": False,
            "matter_current_exchange_route_proved": False,
            "em_closure_claimed": False,
        },
    ]


def _selection_criteria(closeout: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "selector_consumes_authorized_source_bridge_target",
            "status": "accepted",
            "evidence": CONSUMED_TARGET,
            "assessment": (
                "The selector consumes the active target authorized by the A "
                "bridge-admissibility closeout."
            ),
        },
        {
            "row_id": "bridge_closeout_accepted",
            "status": "accepted",
            "evidence": closeout.get("closeout_result"),
            "assessment": (
                "The vacuum U(1) bridge-admissibility rule closeout is "
                "accepted as selector context."
            ),
        },
        {
            "row_id": "source_rule_retained",
            "status": "accepted",
            "evidence": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
            "assessment": (
                "C_source^A = 0 remains retained only as the closed source "
                "admissibility rule."
            ),
        },
        {
            "row_id": "bridge_rule_retained",
            "status": "accepted",
            "evidence": A_BRIDGE_CONSTRAINT_EQUATION,
            "assessment": (
                "C_bridge^A = 0 remains retained only as the closed bridge "
                "admissibility rule."
            ),
        },
        {
            "row_id": "source_bridge_family_closed_but_not_promoted",
            "status": "accepted",
            "evidence": [
                "A_source_and_bridge_admissibility_rule_family_closed=true",
                "A_source_and_bridge_admissibility_rule_family_promoted=false",
            ],
            "assessment": (
                "The A source and bridge rules are closed as admissibility "
                "rules, not promoted as a complete family or physical law."
            ),
        },
        {
            "row_id": "transport_consistency_family_selected",
            "status": "accepted",
            "evidence": SELECTED_A_CK_CONSTRAINT_FAMILY,
            "assessment": (
                "Transport consistency is selected as the next A/C_k family "
                "after source and bridge admissibility."
            ),
        },
        {
            "row_id": "transport_question_matches_A_derivation_chain",
            "status": "accepted",
            "evidence": TRANSPORT_CONSISTENCY_QUESTION,
            "assessment": (
                "The selected family asks whether the admitted vacuum U(1) A "
                "route remains coherent through the derivation chain."
            ),
        },
        {
            "row_id": "transport_candidate_shape_only_previewed",
            "status": "accepted",
            "evidence": TRANSPORT_CANDIDATE_SHAPE_PREVIEW,
            "assessment": (
                "C_transport^A = 0 is only the next packet's shape preview."
            ),
        },
        {
            "row_id": "transport_tuple_preview_recorded_for_next_packet",
            "status": "accepted",
            "evidence": TRANSPORT_CANDIDATE_TUPLE_PREVIEW,
            "assessment": (
                "The transport tuple is recorded only as the next candidate "
                "packet preview."
            ),
        },
        {
            "row_id": "next_transport_candidate_packet_authorized",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": (
                "The next live target is only the A transport-consistency C_k "
                "constraint candidate packet."
            ),
        },
        {
            "row_id": "no_transport_proof_action_variation_current_or_closure",
            "status": "accepted",
            "evidence": [
                "transport_consistency_proved=false",
                "C_k_action_embedding_constructed=false",
                "C_k_variation_executed=false",
                "J_nu_derived=false",
                "sourced_maxwell_equation_derived=false",
                "full_em_closure_claimed=false",
                "qft_gr_closure_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": (
                "The selector does not prove transport consistency, define a "
                "C_k action embedding, execute variation, derive current, "
                "close EM or QFT-GR, or promote the master action."
            ),
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "toe_native_A_ck_constraint_family_selection_after_source_and_bridge_admissibility"
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


def build_toe_native_a_ck_constraint_family_selection_after_source_and_bridge_admissibility(
    *,
    bridge_closeout_path: Path = BRIDGE_CLOSEOUT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    closeout = _read_json(bridge_closeout_path)
    options = _candidate_family_options()
    selection_criteria = _selection_criteria(closeout)
    acceptance_criteria = {
        "consumes_expected_selector_target": (
            closeout.get("schema_id") == BRIDGE_CLOSEOUT_SCHEMA_ID
            and closeout.get("packet_id") == BRIDGE_CLOSEOUT_PACKET_ID
            and closeout.get("outcome_id") == BRIDGE_CLOSEOUT_OUTCOME
            and closeout.get("closeout_result") == BRIDGE_CLOSEOUT_RESULT
            and closeout.get("selected_next_target") == CONSUMED_TARGET
            and closeout.get("accepted") is True
        ),
        "source_and_bridge_rules_preserved": (
            closeout.get("source_candidate_constraint_form")
            == SOURCE_CANDIDATE_CONSTRAINT_FORM
            and closeout.get("source_admissibility_constraint_form")
            == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
            and closeout.get("A_bridge_constraint_form") == A_BRIDGE_CONSTRAINT_FORM
            and closeout.get("A_bridge_constraint_equation")
            == A_BRIDGE_CONSTRAINT_EQUATION
            and closeout.get("bridge_admissibility_constraint_form")
            == A_BRIDGE_CONSTRAINT_EQUATION
            and closeout.get("source_and_bridge_rule_family_contains_count") == 2
        ),
        "bridge_components_preserved": (
            closeout.get("A_bridge_field_equation_match")
            == A_BRIDGE_FIELD_EQUATION_MATCH
            and closeout.get("A_bridge_stress_energy_match")
            == A_BRIDGE_STRESS_ENERGY_MATCH
            and closeout.get("A_bridge_source_residual_match")
            == A_BRIDGE_SOURCE_RESIDUAL_MATCH
        ),
        "vacuum_u1_context_preserved": (
            closeout.get("gauge_group_policy") == GAUGE_GROUP_POLICY
            and closeout.get("A_field_domain_policy") == A_FIELD_DOMAIN_POLICY
            and closeout.get("F_definition_policy") == F_DEFINITION_POLICY
            and closeout.get("vacuum_euler_lagrange_route")
            == VACUUM_EULER_LAGRANGE_ROUTE
            and closeout.get("on_shell_vacuum_conservation_identity")
            == ON_SHELL_VACUUM_CONSERVATION_IDENTITY
            and closeout.get("source_route_still_blocked")
            == SOURCE_ROUTE_STILL_BLOCKED
        ),
        "transport_selection_is_selector_only": (
            SELECTED_A_CK_OPTION_CLASS == "transport_consistency_constraint"
            and SELECTED_A_CK_CONSTRAINT_FAMILY
            == "A_transport_consistency_constraint_family"
            and NEXT_TARGET
            == "prepare_toe_native_A_transport_consistency_ck_constraint_candidate_packet"
        ),
        "selection_options_recorded": (
            len(options) == 4
            and options[0]["selection_status"]
            == "closed_as_retained_context_not_reselected"
            and options[1]["constraint_family_id"]
            == BRIDGE_SELECTED_A_CK_CONSTRAINT_FAMILY
            and options[2]["constraint_family_id"]
            == SELECTED_A_CK_CONSTRAINT_FAMILY
            and options[3]["selection_status"]
            == A_CURRENT_OR_SOURCED_EM_FAMILY_STATUS
        ),
        "no_forbidden_claims_in_closeout": all(
            closeout.get(key) is False
            for key in [
                "bridge_admissibility_proved",
                "bridge_route_alignment_verified",
                "route_consistency_tuple_proved",
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
                "empirical_validation_claimed",
                "master_action_promoted",
            ]
        ),
        "selection_criteria_all_accepted": all(
            row["status"] == "accepted" for row in selection_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else (
            "REMEDIATE_TOE_NATIVE_A_CK_CONSTRAINT_FAMILY_SELECTION_AFTER_SOURCE_"
            "AND_BRIDGE_ADMISSIBILITY"
        )
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_TOE_NATIVE_A_CK_CONSTRAINT_FAMILY_SELECTION_AFTER_SOURCE_AND_"
            "BRIDGE_ADMISSIBILITY"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "TOE_NATIVE_A_CK_CONSTRAINT_FAMILY_SELECTION_AFTER_SOURCE_AND_BRIDGE_"
            "ADMISSIBILITY_REQUIRES_REMEDIATION"
        ),
        "selection_result": SELECTION_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "bridge_closeout_outcome": BRIDGE_CLOSEOUT_OUTCOME,
        "bridge_closeout_result": BRIDGE_CLOSEOUT_RESULT,
        "source_rule_closeout_outcome": SOURCE_RULE_CLOSEOUT_OUTCOME,
        "source_candidate_constraint_id": SOURCE_CANDIDATE_CONSTRAINT_ID,
        "source_candidate_constraint_form": SOURCE_CANDIDATE_CONSTRAINT_FORM,
        "source_admissibility_constraint_form": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        "source_rule_meaning": SOURCE_RULE_MEANING,
        "bridge_selected_A_ck_option_class": BRIDGE_SELECTED_A_CK_OPTION_CLASS,
        "bridge_selected_A_ck_constraint_family": (
            BRIDGE_SELECTED_A_CK_CONSTRAINT_FAMILY
        ),
        "bridge_rule_epistemic_status": BRIDGE_RULE_EPISTEMIC_STATUS,
        "A_bridge_candidate_id": A_BRIDGE_CANDIDATE_ID,
        "A_bridge_constraint_form": A_BRIDGE_CONSTRAINT_FORM,
        "A_bridge_constraint_equation": A_BRIDGE_CONSTRAINT_EQUATION,
        "bridge_admissibility_constraint_form": A_BRIDGE_CONSTRAINT_EQUATION,
        "A_bridge_field_equation_match": A_BRIDGE_FIELD_EQUATION_MATCH,
        "A_bridge_stress_energy_match": A_BRIDGE_STRESS_ENERGY_MATCH,
        "A_bridge_source_residual_match": A_BRIDGE_SOURCE_RESIDUAL_MATCH,
        "bridge_rule_meaning": BRIDGE_RULE_MEANING,
        "gauge_group_policy": GAUGE_GROUP_POLICY,
        "A_field_domain_policy": A_FIELD_DOMAIN_POLICY,
        "F_definition_policy": F_DEFINITION_POLICY,
        "vacuum_euler_lagrange_route": VACUUM_EULER_LAGRANGE_ROUTE,
        "on_shell_vacuum_conservation_identity": (
            ON_SHELL_VACUUM_CONSERVATION_IDENTITY
        ),
        "source_route_still_blocked": SOURCE_ROUTE_STILL_BLOCKED,
        "closed_A_ck_rule_family_count": 2,
        "closed_A_ck_rule_roles": ["source admissibility", "bridge admissibility"],
        "A_ck_source_bridge_rule_family_summary": [
            {
                "rule_id": "A_source_admissibility_ck_rule",
                "rule_form": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
                "plain_meaning": SOURCE_RULE_MEANING,
                "status": "closed_as_admissibility_only",
                "action_term": False,
                "varied": False,
                "derives_current_or_sourced_maxwell": False,
            },
            {
                "rule_id": "A_bridge_admissibility_ck_rule",
                "rule_form": A_BRIDGE_CONSTRAINT_EQUATION,
                "plain_meaning": BRIDGE_RULE_MEANING,
                "status": "closed_as_admissibility_only",
                "action_term": False,
                "varied": False,
                "derives_current_or_sourced_maxwell": False,
            },
        ],
        "selected_A_ck_option_class": SELECTED_A_CK_OPTION_CLASS,
        "selected_A_ck_constraint_family": SELECTED_A_CK_CONSTRAINT_FAMILY,
        "selected_family_selection_status": SELECTED_FAMILY_SELECTION_STATUS,
        "transport_consistency_question": TRANSPORT_CONSISTENCY_QUESTION,
        "transport_candidate_shape_preview": TRANSPORT_CANDIDATE_SHAPE_PREVIEW,
        "transport_candidate_tuple_preview": TRANSPORT_CANDIDATE_TUPLE_PREVIEW,
        "transport_tuple_components": TRANSPORT_TUPLE_COMPONENTS,
        "transport_tuple_component_count": len(TRANSPORT_TUPLE_COMPONENTS),
        "transport_candidate_plain_meaning": TRANSPORT_CANDIDATE_PLAIN_MEANING,
        "transport_chain_steps": TRANSPORT_CHAIN_STEPS,
        "transport_chain_form": TRANSPORT_CHAIN_FORM,
        "transport_chain_step_count": len(TRANSPORT_CHAIN_STEPS),
        "candidate_family_options": options,
        "candidate_family_option_count": len(options),
        "selection_criteria": selection_criteria,
        "selection_criteria_count": len(selection_criteria),
        "selection_criteria_accepted_count": sum(
            1 for row in selection_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "selector_target_prepared": True,
        "selector_target_accepted": True,
        "selection_executed": True,
        "transport_consistency_family_selected": True,
        "transport_consistency_recommended_only": False,
        "transport_consistency_candidate_packet_authorized": True,
        "transport_consistency_candidate_packet_prepared": False,
        "transport_candidate_shape_preview_recorded": True,
        "transport_candidate_tuple_preview_recorded": True,
        "transport_chain_recorded": True,
        "source_and_bridge_rules_retained_as_context": True,
        "source_admissibility_rule_retained_as_context": True,
        "bridge_admissibility_rule_retained_as_context": True,
        "source_admissibility_family_reselected": False,
        "bridge_admissibility_family_reselected": False,
        "source_bridge_family_promoted": False,
        "transport_candidate_constructed": False,
        "transport_candidate_functional_defined": False,
        "transport_candidate_functional_selected": False,
        "transport_proof_claimed": False,
        "transport_consistency_proved": False,
        "transport_chain_compatibility_proved": False,
        "residual_regime_route_proved": False,
        "concrete_ck_functional_selected": False,
        "concrete_ck_functional_defined": False,
        "fully_concrete_ck_functional_selected": False,
        "fully_concrete_ck_functional_defined": False,
        "candidate_action_insertion_executed": False,
        "constraint_as_action_term_selected": False,
        "constraint_term_selected": False,
        "ck_action_embedding_claimed": False,
        "ck_action_embedding_selected": False,
        "ck_action_embedding_constructed": False,
        "C_k_action_embedding_selected": False,
        "C_k_action_embedding_constructed": False,
        "ck_variation_executed": False,
        "ck_variation_authorized": False,
        "C_k_variation_executed": False,
        "C_k_variation_authorized": False,
        "lambda_variation_executed": False,
        "metric_variation_executed": False,
        "A_variation_executed": False,
        "new_conservation_proof_claimed": False,
        "source_admissibility_proved": False,
        "source_conservation_proved": False,
        "bridge_admissibility_proved": False,
        "bridge_route_alignment_verified": False,
        "route_consistency_tuple_proved": False,
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
        "claim_level": (
            "Level 3 selector; selects the A transport-consistency C_k family "
            "after source and bridge admissibility closeout without preparing "
            "the transport candidate, proving transport, deriving current, "
            "executing C_k variation, or promoting the master action"
        ),
        "claim_ceiling": (
            "abstract A-relevant C_k family selection only no transport proof "
            "no C_k action embedding no C_k variation no J^nu derivation no "
            "psi-current route no external-current native derivation no "
            "sourced Maxwell no matter-current exchange no full EM closure no "
            "QFT-GR closure no semiclassical coupling no empirical validation "
            "no master-action promotion no Phase 2 authorization"
        ),
        "mathematical_statement": (
            "The selector retains C_source^A = 0 and C_bridge^A = 0 as closed "
            "vacuum U(1) admissibility-only A/C_k rule context and selects "
            "A_transport_consistency_constraint_family for the next candidate "
            "packet. The next packet may test C_transport^A = 0 as a "
            "derivation-chain stability rule, but no transport rule is "
            "constructed or proved here."
        ),
        "non_claim_boundary": (
            "This selector only chooses A_transport_consistency_constraint_family "
            "as the next abstract A/C_k family after source and bridge "
            "admissibility. It records C_transport^A = 0 and C_transport^A := "
            "(Transport_ACTION_VARIATION^A, Transport_VARIATION_STRESS_ENERGY^A, "
            "Transport_STRESS_ENERGY_SOURCE^A, Transport_SOURCE_BRIDGE^A, "
            "Transport_BRIDGE_RESIDUAL^A) only as the next packet preview. It "
            "does not prepare the transport candidate packet, does not define "
            "a concrete C_transport^A functional, does not prove transport "
            "consistency, does not prove derivation-chain compatibility, does "
            "not embed C_k in the action, does not execute C_k variation, does "
            "not derive J^nu, does not derive a psi-current route, does not "
            "derive an external-current native route, does not derive sourced "
            "Maxwell, does not prove matter/current exchange, does not close "
            "EM, does not close QFT-GR, does not authorize semiclassical "
            "coupling, does not claim empirical validation, does not authorize "
            "Phase 2, records no Phase 2 authorization, and does not promote "
            "the master action."
        ),
        "critical_gate_fail_conditions": [
            "prepare the transport candidate packet in this selector",
            "claim C_transport^A is defined as a concrete functional here",
            "claim transport consistency is proved",
            "embed C_k into the action",
            "execute C_k variation",
            "derive J^nu",
            "derive a psi-current route",
            "derive an external-current native route",
            "derive sourced Maxwell",
            "prove matter-current exchange",
            "claim full EM closure",
            "claim QFT-GR closure",
            "claim semiclassical coupling",
            "promote the master action",
            "claim empirical validation",
            "authorize Phase 2",
        ],
        "validation_policy": _validation_policy(),
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "aggregate_lean_validation_status_for_packet": FULL_TOEFORMAL_STATUS,
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_STATUS,
        "lane_level_lean_targets": [
            (
                "ToeFormal.Derivation."
                "ToeNativeACKConstraintFamilySelectionAfterSourceAndBridgeAdmissibility"
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
            "bridge_closeout_file": _ptr(bridge_closeout_path),
            "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        },
    }


def write_selection(selection: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(selection, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Build the ToE-native A C_k family selector after source and bridge "
            "admissibility."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    selection = (
        build_toe_native_a_ck_constraint_family_selection_after_source_and_bridge_admissibility(
            captured_at_utc=args.captured_at_utc
        )
    )
    path = write_selection(selection, args.out)
    print(
        json.dumps(
            {
                "accepted": selection["accepted"],
                "out": _ptr(path),
                "selected_next_target": selection["selected_next_target"],
                "selection_result": selection["selection_result"],
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
