from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_transport_consistency_ck_functional_embedding_packet_result_review_report import (
    ADMISSIBILITY_ONLY_ROUTE_ID,
    ADMISSIBILITY_ONLY_ROUTE_STATUS,
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    CONSUMED_TARGET as FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW_TARGET,
    DEFAULT_OUT as FUNCTIONAL_EMBEDDING_REVIEW_PATH,
    DIRECT_DYNAMICAL_LAW_INTERPRETATION_ID,
    DIRECT_DYNAMICAL_LAW_INTERPRETATION_STATUS,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    KNOWN_PHI_TRANSPORT_CHAIN_FORM,
    LAGRANGE_MULTIPLIER_ACTION_FORM,
    LAGRANGE_MULTIPLIER_ROUTE_ID,
    LAGRANGE_MULTIPLIER_ROUTE_STATUS,
    LEAN_VALIDATION_POLICY_ID,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME,
    PACKET_ID as FUNCTIONAL_EMBEDDING_REVIEW_PACKET_ID,
    PENALTY_ACTION_FORM,
    PENALTY_ROUTE_ID,
    PENALTY_ROUTE_STATUS,
    REVIEW_RESULT as FUNCTIONAL_EMBEDDING_REVIEW_RESULT,
    SCHEMA_ID as FUNCTIONAL_EMBEDDING_REVIEW_SCHEMA_ID,
    SELECTED_CK_CONSTRAINT_FAMILY,
    SELECTED_CK_OPTION_CLASS,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    THIRD_RULE_CLASSIFICATION,
    TRANSPORT_ACTION_EMBEDDING_CHAIN_FORM,
    TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
    TRANSPORT_CANDIDATE_ID,
    TRANSPORT_CANDIDATE_TYPE,
    TRANSPORT_COMPONENTS,
    TRANSPORT_CONSTRAINT_EQUATION,
    TRANSPORT_CONSTRAINT_FORM,
    TRANSPORT_RULE_CLASSIFICATION,
    TRANSPORT_RULE_EPISTEMIC_STATUS,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-19T00:00:00Z"

SCHEMA_ID = "PHI_TRANSPORT_CONSISTENCY_CK_ADMISSIBILITY_RULE_CLOSEOUT_20260619_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "PHI_TRANSPORT_CONSISTENCY_CK_ADMISSIBILITY_RULE_CLOSEOUT_v0"
CLOSEOUT_RESULT = (
    "PHI_TRANSPORT_CONSISTENCY_CK_ADMISSIBILITY_RULE_CLOSED_AS_DERIVATION_"
    "CHAIN_STABILITY_RULE_NO_ACTION_VARIATION_OR_PROMOTION"
)
OUTCOME_ID = CLOSEOUT_RESULT
PACKET_CLASSIFICATION = (
    "phi_transport_consistency_ck_admissibility_rule_closed_as_derivation_"
    "chain_stability_rule_no_action_variation_or_promotion"
)
NEXT_TARGET = "prepare_phi_ck_source_bridge_transport_rule_family_synthesis_packet"
NEXT_TARGET_KIND = "phi_ck_source_bridge_transport_rule_family_synthesis_packet_preparation"

TRANSPORT_CLOSEOUT_RULE_CLASSIFICATION = "transport-consistency rule candidate"
TRANSPORT_CLOSEOUT_RULE_ROLE = "derivation-chain stability rule"
RULE_FAMILY_SYNTHESIS_OUTCOME_HINT = (
    "PHI_CK_SOURCE_BRIDGE_TRANSPORT_RULE_FAMILY_SYNTHESIS_PACKET_PREPARED_"
    "THREE_ADMISSIBILITY_RULES_SYNTHESIZED_NO_ACTION_VARIATION_OR_PROMOTION"
)
SOURCE_RULE_CLOSEOUT_OUTCOME = (
    "PHI_SOURCE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSED_AS_FIRST_PHI_"
    "RELEVANT_CK_RULE_CANDIDATE_NO_ACTION_VARIATION_OR_PROMOTION"
)
BRIDGE_RULE_CLOSEOUT_OUTCOME = (
    "PHI_BRIDGE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSED_AS_ROUTE_"
    "CONSISTENCY_RULE_NO_ACTION_VARIATION_OR_PROMOTION"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_TRANSPORT_CONSISTENCY_CK_ADMISSIBILITY_RULE_CLOSEOUT_20260619_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiTransportConsistencyCKAdmissibilityRuleCloseout.lean"
)
QFTGR_AGGREGATE_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "QFTGR.lean"
)
CURRENT_TARGET_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CurrentTarget.lean"
)
RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "CurrentAuthority.lean"
)
LEAN_VALIDATION_POLICY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "LEAN_VALIDATION_TIER_POLICY_v0.md"
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
                "interpretation of C_transport^phi = 0."
            ),
        },
        {
            "row_id": "third_phi_relevant_ck_rule_candidate_closed",
            "status": "accepted",
            "evidence": THIRD_RULE_CLASSIFICATION,
            "assessment": (
                "The closeout classifies the transport rule as the third "
                "phi-relevant C_k admissibility rule candidate."
            ),
        },
        {
            "row_id": "transport_tuple_preserved",
            "status": "accepted",
            "evidence": TRANSPORT_CONSTRAINT_FORM,
            "assessment": "The five-component transport tuple is preserved.",
        },
        {
            "row_id": "transport_condition_preserved",
            "status": "accepted",
            "evidence": TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
            "assessment": "C_transport^phi = 0 is preserved as the transport rule.",
        },
        {
            "row_id": "transport_components_preserved_unproved",
            "status": "accepted",
            "evidence": [row["component_form"] for row in TRANSPORT_COMPONENTS],
            "assessment": (
                "The action/variation, variation/bridge, bridge/source, "
                "source/residual, and residual/regime components are carried "
                "forward without proof."
            ),
        },
        {
            "row_id": "source_and_bridge_context_preserved",
            "status": "accepted",
            "evidence": [
                SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
                BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
            ],
            "assessment": (
                "The source- and bridge-admissibility rules remain the "
                "context for the transport rule."
            ),
        },
        {
            "row_id": "closed_as_transport_consistency_rule_candidate",
            "status": "accepted",
            "evidence": [
                TRANSPORT_CLOSEOUT_RULE_CLASSIFICATION,
                TRANSPORT_CLOSEOUT_RULE_ROLE,
                TRANSPORT_RULE_EPISTEMIC_STATUS,
            ],
            "assessment": (
                "The object is closed as an admissibility-only derivation-"
                "chain stability rule candidate."
            ),
        },
        {
            "row_id": "not_action_term_or_dynamical_law",
            "status": "accepted",
            "evidence": [
                "constraint_as_action_term_selected=false",
                "transport_candidate_recorded_as_new_dynamical_law=false",
            ],
            "assessment": (
                "The closeout does not treat the transport rule as an action "
                "term or new dynamical law."
            ),
        },
        {
            "row_id": "multiplier_penalty_and_direct_law_routes_remain_blocked",
            "status": "accepted",
            "evidence": [
                LAGRANGE_MULTIPLIER_ROUTE_STATUS,
                PENALTY_ROUTE_STATUS,
                DIRECT_DYNAMICAL_LAW_INTERPRETATION_STATUS,
            ],
            "assessment": (
                "The multiplier/action route remains blocked, the penalty "
                "route remains unlicensed, and direct dynamical-law "
                "interpretation remains blocked."
            ),
        },
        {
            "row_id": "no_variation_generation_or_potential_derivation",
            "status": "accepted",
            "evidence": [
                "ck_variation_executed=false",
                "phi_generated_by_ck_claimed=false",
                "potential_derived=false",
            ],
            "assessment": (
                "The closeout executes no variation, generates no phi, and "
                "derives no V(phi)."
            ),
        },
        {
            "row_id": "no_transport_proof_qft_gr_closure_or_master_promotion",
            "status": "accepted",
            "evidence": [
                "transport_consistency_proved=false",
                "qft_gr_closure_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": (
                "Transport proof, QFT-GR closure, semiclassical coupling, and "
                "master-action promotion remain unclaimed."
            ),
        },
        {
            "row_id": "full_toeformal_aggregate_recorded_not_run",
            "status": "accepted",
            "evidence": FULL_TOEFORMAL_AGGREGATE_STATUS,
            "assessment": "The full ToeFormal aggregate remains recorded as NOT_RUN.",
        },
        {
            "row_id": "three_rule_family_synthesis_packet_authorized",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": (
                "The next target synthesizes source, bridge, and transport "
                "as a three-rule phi/C_k admissibility family."
            ),
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "phi_transport_consistency_ck_admissibility_rule_closeout",
        "tiered_lean_validation_policy_formalized": True,
        "routine_packet_validation_tiers": [
            "touched Lean marker",
            "smallest affected Lake target",
            "lane aggregate",
            "current authority target",
        ],
        "release_preservation_validation": "full ToeFormal aggregate when feasible",
        "toeformal_import_update_requires_preservation_status": True,
        "aggregate_lean_validation_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "aggregate_lean_validation_status_allowed_values": ["NOT_RUN"],
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_phi_transport_consistency_ck_admissibility_rule_closeout(
    *,
    functional_embedding_review_path: Path = FUNCTIONAL_EMBEDDING_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(functional_embedding_review_path)
    closeout_criteria = _closeout_criteria(review)
    acceptance_criteria = {
        "consumes_expected_closeout_target": (
            review.get("schema_id") == FUNCTIONAL_EMBEDDING_REVIEW_SCHEMA_ID
            and review.get("packet_id") == FUNCTIONAL_EMBEDDING_REVIEW_PACKET_ID
            and review.get("outcome_id") == FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME
            and review.get("review_result") == FUNCTIONAL_EMBEDDING_REVIEW_RESULT
            and review.get("selected_next_target") == CONSUMED_TARGET
            and review.get("accepted") is True
        ),
        "transport_rule_preserved": (
            review.get("transport_candidate_id") == TRANSPORT_CANDIDATE_ID
            and review.get("transport_candidate_type") == TRANSPORT_CANDIDATE_TYPE
            and review.get("transport_rule_classification")
            == TRANSPORT_RULE_CLASSIFICATION
            and review.get("transport_rule_epistemic_status")
            == TRANSPORT_RULE_EPISTEMIC_STATUS
            and review.get("transport_constraint_form") == TRANSPORT_CONSTRAINT_FORM
            and review.get("transport_constraint_equation")
            == TRANSPORT_CONSTRAINT_EQUATION
            and review.get("transport_admissibility_constraint_form")
            == TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
            and review.get("transport_component_count") == len(TRANSPORT_COMPONENTS)
        ),
        "source_bridge_context_preserved": (
            review.get("source_candidate_constraint_id")
            == SOURCE_CANDIDATE_CONSTRAINT_ID
            and review.get("source_candidate_constraint_form")
            == SOURCE_CANDIDATE_CONSTRAINT_FORM
            and review.get("source_candidate_constraint_equation")
            == SOURCE_CANDIDATE_CONSTRAINT_EQUATION
            and review.get("source_admissibility_constraint_form")
            == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
            and review.get("bridge_constraint_form") == BRIDGE_CONSTRAINT_FORM
            and review.get("bridge_constraint_equation")
            == BRIDGE_CONSTRAINT_EQUATION
            and review.get("bridge_admissibility_constraint_form")
            == BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
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
            and review.get("penalty_route_recorded") is True
            and review.get("penalty_route_licensed") is False
            and review.get("direct_dynamical_law_interpretation_blocked") is True
            and review.get("direct_dynamical_law_interpretation_selected") is False
            and review.get("lagrange_multiplier_action_form")
            == LAGRANGE_MULTIPLIER_ACTION_FORM
            and review.get("penalty_action_form") == PENALTY_ACTION_FORM
        ),
        "no_variation_or_action_embedding": all(
            review.get(key) is False
            for key in [
                "dynamical_action_embedding_selected",
                "constraint_as_action_term_selected",
                "transport_candidate_recorded_as_action_term",
                "transport_candidate_recorded_as_new_dynamical_law",
                "transport_functional_selected",
                "transport_candidate_functional_defined",
                "transport_candidate_functional_selected",
                "component_pairing_rule_selected",
                "transport_map_domains_codomains_selected",
                "constraint_multiplier_type_selected",
                "constraint_term_selected",
                "multiplier_type_selected",
                "multiplier_domain_selected",
                "covariance_of_multiplier_pairing_established",
                "boundary_terms_controlled",
                "boundary_regime_projection_controlled",
                "variation_policy_for_embedding_selected",
                "heterogeneous_tuple_norm_defined",
                "candidate_action_insertion_executed",
                "ck_variation_executed",
                "lambda_variation_executed",
                "metric_variation_of_candidate_executed",
                "phi_variation_of_candidate_executed",
                "penalty_variation_executed",
            ]
        ),
        "no_forbidden_claims": all(
            review.get(key) is False
            for key in [
                "penalty_route_licensed",
                "direct_dynamical_law_interpretation_selected",
                "fully_concrete_ck_functional_selected",
                "fully_concrete_ck_functional_defined",
                "concrete_ck_functional_selected",
                "concrete_ck_functional_defined",
                "ck_action_embedding_claimed",
                "transport_candidate_rule_proved",
                "transport_consistency_claimed",
                "transport_consistency_proved",
                "transport_proof_claimed",
                "transport_components_proved",
                "full_route_alignment_proof_claimed",
                "full_route_alignment_proved",
                "route_chain_compatibility_proved",
                "source_admissibility_proved",
                "bridge_admissibility_proved",
                "phi_generated_by_ck_claimed",
                "phi_generation_theorem_claimed",
                "native_generation_theorem_claimed",
                "derived_v_phi_claimed",
                "v_phi_derivation_claimed",
                "potential_derived",
                "new_conservation_proof_claimed",
                "new_source_admissibility_proof_claimed",
                "source_admissibility_claimed",
                "qft_gr_closure_claimed",
                "qft_gr_solved",
                "qft_gr_seam_closed",
                "semiclassical_coupling_authorized",
                "semiclassical_coupling_claimed",
                "master_action_promoted",
                "master_action_promotion_authorized",
                "canonical_master_action_promoted",
                "toe_native_matter_derivation_claimed",
                "standard_model_derivation_claimed",
                "empirical_validation_claimed",
                "public_readiness_claimed",
                "phase2_readiness_claim",
                "pillar_completion_inferred",
                "seam_closure_claim",
            ]
        ),
        "full_toeformal_aggregate_recorded_not_run": (
            review.get("aggregate_lean_validation_status_for_packet")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and review.get("full_toeformal_aggregate_status_for_packet")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and review.get("full_toeformal_aggregate_passed") is False
            and review.get("full_toeformal_aggregate_failed") is False
            and review.get("full_toeformal_aggregate_timed_out") is False
        ),
        "three_rule_family_synthesis_target_selected": (
            NEXT_TARGET
            == "prepare_phi_ck_source_bridge_transport_rule_family_synthesis_packet"
        ),
        "closeout_criteria_all_accepted": all(
            row["status"] == "accepted" for row in closeout_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_PHI_TRANSPORT_CONSISTENCY_CK_ADMISSIBILITY_RULE_CLOSEOUT"
    )
    transport_component_forms = [row["component_form"] for row in TRANSPORT_COMPONENTS]
    rule_family_summary = [
        {
            "rule_id": "phi_source_admissibility_ck_rule",
            "rule_form": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
            "plain_meaning": "phi may source gravity only if conserved",
            "status": "closed_as_admissibility_only",
            "action_term": False,
            "derives_phi_or_v_phi": False,
        },
        {
            "rule_id": "phi_bridge_admissibility_ck_rule",
            "rule_form": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
            "plain_meaning": (
                "the phi route is valid only if the master-action route "
                "matches the scalar witness/source route"
            ),
            "status": "closed_as_admissibility_only",
            "action_term": False,
            "derives_phi_or_v_phi": False,
        },
        {
            "rule_id": "phi_transport_consistency_ck_rule",
            "rule_form": TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
            "plain_meaning": (
                "the phi route is valid only if it remains coherent across "
                "the derivation chain"
            ),
            "status": "closed_as_admissibility_only",
            "action_term": False,
            "derives_phi_or_v_phi": False,
        },
    ]
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_PHI_TRANSPORT_CONSISTENCY_CK_ADMISSIBILITY_RULE_CLOSEOUT",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PHI_TRANSPORT_CONSISTENCY_CK_ADMISSIBILITY_RULE_CLOSEOUT_REQUIRES_REMEDIATION",
        "closeout_result": CLOSEOUT_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "functional_embedding_review_outcome": FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME,
        "functional_embedding_review_result": FUNCTIONAL_EMBEDDING_REVIEW_RESULT,
        "functional_embedding_packet_result_review_target": (
            FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW_TARGET
        ),
        "selected_ck_option_class": SELECTED_CK_OPTION_CLASS,
        "selected_ck_constraint_family": SELECTED_CK_CONSTRAINT_FAMILY,
        "third_phi_relevant_ck_admissibility_rule_candidate_classification": (
            THIRD_RULE_CLASSIFICATION
        ),
        "transport_rule_classification": TRANSPORT_RULE_CLASSIFICATION,
        "transport_closeout_rule_classification": TRANSPORT_CLOSEOUT_RULE_CLASSIFICATION,
        "transport_rule_role": TRANSPORT_CLOSEOUT_RULE_ROLE,
        "transport_rule_epistemic_status": TRANSPORT_RULE_EPISTEMIC_STATUS,
        "transport_candidate_id": TRANSPORT_CANDIDATE_ID,
        "transport_candidate_type": TRANSPORT_CANDIDATE_TYPE,
        "transport_constraint_form": TRANSPORT_CONSTRAINT_FORM,
        "transport_constraint_equation": TRANSPORT_CONSTRAINT_EQUATION,
        "transport_admissibility_constraint_form": TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
        "transport_component_count": len(TRANSPORT_COMPONENTS),
        "transport_component_forms": transport_component_forms,
        "transport_components_preserved": True,
        "transport_action_embedding_chain_form": TRANSPORT_ACTION_EMBEDDING_CHAIN_FORM,
        "known_phi_transport_chain_form": KNOWN_PHI_TRANSPORT_CHAIN_FORM,
        "source_rule_closeout_outcome": SOURCE_RULE_CLOSEOUT_OUTCOME,
        "source_candidate_constraint_id": SOURCE_CANDIDATE_CONSTRAINT_ID,
        "source_candidate_constraint_form": SOURCE_CANDIDATE_CONSTRAINT_FORM,
        "source_candidate_constraint_equation": SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
        "source_admissibility_constraint_form": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        "bridge_rule_closeout_outcome": BRIDGE_RULE_CLOSEOUT_OUTCOME,
        "bridge_constraint_form": BRIDGE_CONSTRAINT_FORM,
        "bridge_constraint_equation": BRIDGE_CONSTRAINT_EQUATION,
        "bridge_admissibility_constraint_form": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        "selected_embedding_route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
        "admissibility_only_route_status": ADMISSIBILITY_ONLY_ROUTE_STATUS,
        "embedding_route_count": 3,
        "lagrange_multiplier_route_id": LAGRANGE_MULTIPLIER_ROUTE_ID,
        "lagrange_multiplier_route_status": LAGRANGE_MULTIPLIER_ROUTE_STATUS,
        "lagrange_multiplier_action_form": LAGRANGE_MULTIPLIER_ACTION_FORM,
        "penalty_route_id": PENALTY_ROUTE_ID,
        "penalty_route_status": PENALTY_ROUTE_STATUS,
        "penalty_action_form": PENALTY_ACTION_FORM,
        "direct_dynamical_law_interpretation_id": (
            DIRECT_DYNAMICAL_LAW_INTERPRETATION_ID
        ),
        "direct_dynamical_law_interpretation_status": (
            DIRECT_DYNAMICAL_LAW_INTERPRETATION_STATUS
        ),
        "closeout_criteria": closeout_criteria,
        "closeout_criteria_count": len(closeout_criteria),
        "closeout_criteria_accepted_count": sum(
            1 for row in closeout_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "admissibility_rule_closeout_prepared": True,
        "admissibility_rule_closeout_accepted": True,
        "third_phi_relevant_ck_admissibility_rule_candidate_closed": True,
        "transport_consistency_rule_candidate_closed": True,
        "derivation_chain_stability_rule_closed": True,
        "transport_admissibility_rule_closed_as_derivation_chain_stability_rule": True,
        "admissibility_only_route_selected": True,
        "admissibility_only_interpretation_retained": True,
        "constraint_as_admissibility_rule_selected": True,
        "constraint_as_action_term_selected": False,
        "dynamical_action_embedding_selected": False,
        "dynamical_action_embedding_not_assumed": True,
        "candidate_recorded_as_rule_only": True,
        "candidate_recorded_as_new_physical_law": False,
        "candidate_recorded_as_action_term": False,
        "transport_candidate_recorded_as_action_term": False,
        "transport_candidate_recorded_as_new_dynamical_law": False,
        "transport_tuple_carried_forward": True,
        "transport_constraint_carried_forward": True,
        "transport_components_carried_forward": True,
        "transport_components_preserved_unproved": True,
        "source_and_bridge_context_preserved": True,
        "known_phi_chain_preserved": True,
        "lagrange_multiplier_route_recorded": True,
        "lagrange_multiplier_route_blocked": True,
        "penalty_route_recorded": True,
        "penalty_route_licensed": False,
        "direct_dynamical_law_interpretation_recorded": True,
        "direct_dynamical_law_interpretation_blocked": True,
        "direct_dynamical_law_interpretation_selected": False,
        "three_rule_family_synthesis_packet_authorized": True,
        "three_rule_family_synthesis_packet_prepared": False,
        "three_rule_family_synthesis_outcome_hint": RULE_FAMILY_SYNTHESIS_OUTCOME_HINT,
        "phi_ck_admissibility_rule_family_contains_count": 3,
        "phi_ck_source_bridge_transport_rule_family_summary": rule_family_summary,
        "source_admissibility_rule_synthesis_entry_preserved": True,
        "bridge_admissibility_rule_synthesis_entry_preserved": True,
        "transport_consistency_rule_synthesis_entry_preserved": True,
        "another_phi_derivation_selected": False,
        "master_action_surface_rotation_selected": False,
        "qft_gr_semiclassical_prerequisite_return_selected": False,
        "public_explanatory_section_selected": False,
        "proof_depth_label": (
            "THIRD_PHI_RELEVANT_CK_ADMISSIBILITY_RULE_CANDIDATE_CLOSED_"
            "NO_ACTION_VARIATION"
        ),
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
        "penalty_would_change_dynamics": True,
        "fully_concrete_ck_functional_selected": False,
        "fully_concrete_ck_functional_defined": False,
        "concrete_ck_functional_selected": False,
        "concrete_ck_functional_defined": False,
        "ck_functional_formula_fully_defined": False,
        "ck_functional_formula_selected": False,
        "candidate_action_insertion_executed": False,
        "ck_variation_executed": False,
        "ck_variation_authorized": False,
        "lambda_variation_executed": False,
        "metric_variation_of_candidate_executed": False,
        "phi_variation_of_candidate_executed": False,
        "penalty_variation_executed": False,
        "ck_family_claimed_as_physical_law": False,
        "ck_action_embedding_claimed": False,
        "transport_candidate_rule_proved": False,
        "transport_consistency_claimed": False,
        "transport_consistency_proved": False,
        "transport_proof_claimed": False,
        "transport_components_proved": False,
        "full_route_alignment_proof_claimed": False,
        "full_route_alignment_proved": False,
        "route_chain_compatibility_proved": False,
        "source_admissibility_proved": False,
        "bridge_admissibility_proved": False,
        "native_phi_derivation_claimed": False,
        "phi_generated_by_ck_claimed": False,
        "phi_generation_theorem_claimed": False,
        "native_generation_theorem_claimed": False,
        "derived_v_phi_claimed": False,
        "v_phi_derivation_claimed": False,
        "potential_derived": False,
        "new_conservation_proof_claimed": False,
        "new_source_admissibility_proof_claimed": False,
        "source_admissibility_claimed": False,
        "source_conservation_claimed": False,
        "weak_conservation_claimed": False,
        "bianchi_compatibility_claimed": False,
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
        "toe_native_matter_derivation_claimed": False,
        "toe_native_matter_sector_derived": False,
        "toe_native_matter_sector_defined": False,
        "standard_model_derivation_claimed": False,
        "empirical_validation_claimed": False,
        "public_readiness_claimed": False,
        "public_submission_authorized": False,
        "phase2_readiness_claim": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "mathematical_statement": (
            "The phi transport-consistency C_k candidate is closed as a "
            "derivation-chain stability admissibility-rule candidate: "
            "C_transport^phi := (Transport_ACTION_VARIATION^phi, "
            "Transport_VARIATION_BRIDGE^phi, Transport_BRIDGE_SOURCE^phi, "
            "Transport_SOURCE_RESIDUAL^phi, Transport_RESIDUAL_REGIME^phi), "
            "with rule C_transport^phi = 0. It states that the phi route is "
            "admitted only if the transported equation/source/residual "
            "objects remain compatible through the derivation chain. The "
            "closeout is admissibility-only and executes no action variation."
        ),
        "non_claim_boundary": (
            "This closeout records the third phi-relevant C_k admissibility "
            "rule candidate only. It keeps C_transport^phi = 0 as a "
            "transport-consistency derivation-chain stability admissibility-"
            "rule candidate, not as an action term, not as a transport proof, "
            "not as a native phi generation theorem, not as V(phi) "
            "derivation, not as QFT-GR closure, and not as master-action "
            "promotion. It does not functionalize C_transport^phi, does not "
            "embed it in S_C, does not define a C_k action term, does not "
            "select Lambda_transport or a multiplier type, does not select "
            "transport-map domains/codomains, does not define a norm over "
            "the heterogeneous transport tuple, does not license the penalty "
            "route, does not interpret the candidate as a direct dynamical "
            "law, does not execute C_k variation, does not vary "
            "Lambda_transport, phi, or g, does not prove transport "
            "consistency, does not prove full route alignment, does not prove "
            "any transport component, does not claim phi generation, does not "
            "derive V(phi), does not prove new conservation, does not prove "
            "source admissibility, does not close QFT-GR, does not authorize "
            "semiclassical coupling, does not promote the master action, "
            "does not claim empirical validation, and does not authorize "
            "public readiness. The full ToeFormal aggregate is recorded as "
            "NOT_RUN for this closeout. The next target is a three-rule "
            "source/bridge/transport phi/C_k synthesis packet, not another "
            "immediate phi derivation."
        ),
        "critical_gate_fail_conditions": [
            "claim C_transport^phi = 0 is an action term",
            "claim C_k action embedding",
            "execute C_k variation",
            "claim the multiplier/action route is selected",
            "claim the penalty route is licensed",
            "claim direct dynamical-law interpretation is selected",
            "claim transport consistency is proved",
            "claim full route alignment is proved",
            "claim any transport component is proved",
            "claim phi generation",
            "claim V(phi) derivation",
            "claim new conservation proof",
            "claim new source-admissibility proof",
            "claim QFT-GR closure",
            "claim semiclassical coupling",
            "promote the master action",
            "claim empirical validation",
            "record full ToeFormal aggregate as passed, failed, or timed out",
            "start another phi derivation before the three-rule family synthesis packet",
        ],
        "validation_policy": _validation_policy(),
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "aggregate_lean_validation_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.PhiTransportConsistencyCKAdmissibilityRuleCloseout",
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
            "Build the phi transport-consistency C_k admissibility rule closeout."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    closeout = build_phi_transport_consistency_ck_admissibility_rule_closeout(
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
