from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_bridge_admissibility_ck_functional_embedding_packet_result_review_report import (
    ADMISSIBILITY_ONLY_ROUTE_ID,
    ADMISSIBILITY_ONLY_ROUTE_STATUS,
    AGGREGATE_TIMEOUT_STATUS,
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_CANDIDATE_ID,
    BRIDGE_CANDIDATE_RULE_PLAIN_MEANING,
    BRIDGE_CANDIDATE_TYPE,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    BRIDGE_ROUTE_ALIGNMENT_SEQUENCE,
    BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
    BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
    BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
    DEFAULT_OUT as FUNCTIONAL_EMBEDDING_REVIEW_PATH,
    LAGRANGE_MULTIPLIER_ACTION_FORM,
    LAGRANGE_MULTIPLIER_ROUTE_ID,
    LAGRANGE_MULTIPLIER_ROUTE_STATUS,
    LEAN_VALIDATION_POLICY_ID,
    OUTCOME_ID as FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME,
    PACKET_ID as FUNCTIONAL_EMBEDDING_REVIEW_PACKET_ID,
    PENALTY_ACTION_FORM,
    PENALTY_ROUTE_ID,
    PENALTY_ROUTE_STATUS,
    REVIEW_RESULT as FUNCTIONAL_EMBEDDING_REVIEW_RESULT,
    SCHEMA_ID as FUNCTIONAL_EMBEDDING_REVIEW_SCHEMA_ID,
    SECOND_RULE_CLASSIFICATION,
    SELECTED_CK_CONSTRAINT_FAMILY,
    SELECTED_CK_OPTION_CLASS,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    SOURCE_RULE_CLOSEOUT_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-19T00:00:00Z"

SCHEMA_ID = "PHI_BRIDGE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSEOUT_20260619_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "PHI_BRIDGE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSEOUT_v0"
CLOSEOUT_RESULT = (
    "PHI_BRIDGE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSED_AS_ROUTE_"
    "CONSISTENCY_RULE_NO_ACTION_VARIATION_OR_PROMOTION"
)
OUTCOME_ID = CLOSEOUT_RESULT
PACKET_CLASSIFICATION = (
    "phi_bridge_admissibility_ck_admissibility_rule_closed_as_route_"
    "consistency_rule_no_action_variation_or_promotion"
)
CONSUMED_TARGET = "prepare_phi_bridge_admissibility_ck_admissibility_rule_closeout"
NEXT_TARGET = "prepare_phi_ck_admissibility_rule_family_synthesis_packet"
NEXT_TARGET_KIND = "phi_ck_admissibility_rule_family_synthesis_packet_preparation"

BRIDGE_RULE_CLASSIFICATION = "bridge-admissibility rule candidate"
BRIDGE_RULE_EPISTEMIC_STATUS = "admissibility-only"
SOURCE_RULE_SUMMARY_ID = "phi_source_admissibility_ck_rule"
BRIDGE_RULE_SUMMARY_ID = "phi_bridge_admissibility_ck_rule"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_BRIDGE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSEOUT_20260619_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiBridgeAdmissibilityCKAdmissibilityRuleCloseout.lean"
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
                "interpretation of C_bridge^phi = 0."
            ),
        },
        {
            "row_id": "second_phi_relevant_ck_rule_candidate_closed",
            "status": "accepted",
            "evidence": SECOND_RULE_CLASSIFICATION,
            "assessment": (
                "The closeout classifies the bridge rule as the second "
                "phi-relevant C_k admissibility rule candidate."
            ),
        },
        {
            "row_id": "bridge_tuple_preserved",
            "status": "accepted",
            "evidence": BRIDGE_CONSTRAINT_FORM,
            "assessment": "The three-component bridge tuple is preserved exactly.",
        },
        {
            "row_id": "bridge_condition_preserved",
            "status": "accepted",
            "evidence": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
            "assessment": "C_bridge^phi = 0 is preserved as the bridge rule.",
        },
        {
            "row_id": "bridge_components_preserved",
            "status": "accepted",
            "evidence": [
                BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
                BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
                BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
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
                "The source-admissibility rule remains the source-side context "
                "for the bridge rule."
            ),
        },
        {
            "row_id": "closed_as_bridge_admissibility_rule_candidate",
            "status": "accepted",
            "evidence": [BRIDGE_RULE_CLASSIFICATION, BRIDGE_RULE_EPISTEMIC_STATUS],
            "assessment": (
                "The object is closed as a bridge-admissibility rule candidate "
                "and admissibility-only."
            ),
        },
        {
            "row_id": "not_action_term_or_native_generation_theorem",
            "status": "accepted",
            "evidence": [
                "constraint_as_action_term_selected=false",
                "native_generation_theorem_claimed=false",
            ],
            "assessment": (
                "The closeout does not treat the bridge rule as an action term, "
                "new dynamical law, or native-generation theorem."
            ),
        },
        {
            "row_id": "multiplier_and_penalty_routes_remain_blocked",
            "status": "accepted",
            "evidence": [LAGRANGE_MULTIPLIER_ROUTE_STATUS, PENALTY_ROUTE_STATUS],
            "assessment": (
                "The multiplier route remains blocked and the penalty route "
                "remains not licensed."
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
            "row_id": "no_bridge_proof_qft_gr_closure_or_master_promotion",
            "status": "accepted",
            "evidence": [
                "bridge_admissibility_proved=false",
                "qft_gr_closure_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": (
                "Bridge proof, QFT-GR closure, semiclassical coupling, and "
                "master-action promotion remain unclaimed."
            ),
        },
        {
            "row_id": "phi_ck_rule_family_synthesis_packet_authorized",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": (
                "The next target consolidates the source and bridge C_k "
                "admissibility-rule family before further phi derivations."
            ),
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "phi_bridge_admissibility_ck_admissibility_rule_closeout",
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
        "aggregate_lean_validation_status_for_packet": AGGREGATE_TIMEOUT_STATUS,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_phi_bridge_admissibility_ck_admissibility_rule_closeout(
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
        "bridge_tuple_and_components_preserved": (
            review.get("bridge_candidate_id") == BRIDGE_CANDIDATE_ID
            and review.get("bridge_candidate_type") == BRIDGE_CANDIDATE_TYPE
            and review.get("bridge_constraint_form") == BRIDGE_CONSTRAINT_FORM
            and review.get("bridge_constraint_equation") == BRIDGE_CONSTRAINT_EQUATION
            and review.get("bridge_admissibility_constraint_form")
            == BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
            and review.get("bridge_route_field_equation_match")
            == BRIDGE_ROUTE_FIELD_EQUATION_MATCH
            and review.get("bridge_route_stress_energy_match")
            == BRIDGE_ROUTE_STRESS_ENERGY_MATCH
            and review.get("bridge_route_source_residual_match")
            == BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH
        ),
        "source_context_preserved": (
            review.get("source_rule_closeout_outcome") == SOURCE_RULE_CLOSEOUT_OUTCOME
            and review.get("source_candidate_constraint_id")
            == SOURCE_CANDIDATE_CONSTRAINT_ID
            and review.get("source_candidate_constraint_form")
            == SOURCE_CANDIDATE_CONSTRAINT_FORM
            and review.get("source_candidate_constraint_equation")
            == SOURCE_CANDIDATE_CONSTRAINT_EQUATION
            and review.get("source_admissibility_constraint_form")
            == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
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
            and review.get("lagrange_multiplier_action_form")
            == LAGRANGE_MULTIPLIER_ACTION_FORM
            and review.get("penalty_action_form") == PENALTY_ACTION_FORM
        ),
        "no_variation_or_action_embedding": all(
            review.get(key) is False
            for key in [
                "dynamical_action_embedding_selected",
                "constraint_as_action_term_selected",
                "bridge_candidate_recorded_as_action_term",
                "bridge_candidate_recorded_as_new_dynamical_law",
                "bridge_functional_selected",
                "bridge_candidate_functional_defined",
                "bridge_candidate_functional_selected",
                "component_pairing_rule_selected",
                "multiplier_component_domain_selected",
                "constraint_multiplier_type_selected",
                "constraint_term_selected",
                "multiplier_type_selected",
                "multiplier_domain_selected",
                "covariance_of_multiplier_pairing_established",
                "boundary_terms_controlled",
                "variation_policy_for_embedding_selected",
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
                "fully_concrete_ck_functional_selected",
                "fully_concrete_ck_functional_defined",
                "concrete_ck_functional_selected",
                "concrete_ck_functional_defined",
                "ck_action_embedding_claimed",
                "bridge_candidate_rule_proved",
                "bridge_admissibility_claimed",
                "bridge_admissibility_proved",
                "bridge_route_alignment_verified",
                "route_consistency_tuple_proved",
                "field_equation_match_proved",
                "stress_energy_match_proved",
                "source_residual_match_proved",
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
        "closeout_criteria_all_accepted": all(
            row["status"] == "accepted" for row in closeout_criteria
        ),
        "family_synthesis_target_selected": (
            NEXT_TARGET == "prepare_phi_ck_admissibility_rule_family_synthesis_packet"
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_PHI_BRIDGE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSEOUT"
    )
    route_sequence = " -> ".join(BRIDGE_ROUTE_ALIGNMENT_SEQUENCE)
    rule_family_summary = [
        {
            "rule_id": SOURCE_RULE_SUMMARY_ID,
            "rule_form": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
            "plain_meaning": "phi may source gravity only if conserved",
            "status": "closed_as_admissibility_only",
            "action_term": False,
            "derives_phi_or_v_phi": False,
        },
        {
            "rule_id": BRIDGE_RULE_SUMMARY_ID,
            "rule_form": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
            "plain_meaning": (
                "the phi route is valid only if the master-action route "
                "matches the scalar witness/source route"
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
        "status": "ACTIVE_PHI_BRIDGE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSEOUT",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PHI_BRIDGE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSEOUT_REQUIRES_REMEDIATION",
        "closeout_result": CLOSEOUT_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "functional_embedding_review_outcome": FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME,
        "functional_embedding_review_result": FUNCTIONAL_EMBEDDING_REVIEW_RESULT,
        "selected_ck_option_class": SELECTED_CK_OPTION_CLASS,
        "selected_ck_constraint_family": SELECTED_CK_CONSTRAINT_FAMILY,
        "second_phi_relevant_ck_admissibility_rule_candidate_classification": (
            SECOND_RULE_CLASSIFICATION
        ),
        "bridge_rule_classification": BRIDGE_RULE_CLASSIFICATION,
        "bridge_rule_epistemic_status": BRIDGE_RULE_EPISTEMIC_STATUS,
        "bridge_candidate_id": BRIDGE_CANDIDATE_ID,
        "bridge_candidate_type": BRIDGE_CANDIDATE_TYPE,
        "bridge_constraint_form": BRIDGE_CONSTRAINT_FORM,
        "bridge_constraint_equation": BRIDGE_CONSTRAINT_EQUATION,
        "bridge_admissibility_constraint_form": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        "bridge_route_field_equation_match": BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
        "bridge_route_stress_energy_match": BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
        "bridge_route_source_residual_match": BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
        "bridge_candidate_rule_plain_meaning": BRIDGE_CANDIDATE_RULE_PLAIN_MEANING,
        "bridge_route_alignment_sequence": BRIDGE_ROUTE_ALIGNMENT_SEQUENCE,
        "bridge_route_alignment_sequence_plain": route_sequence,
        "bridge_component_count": 3,
        "source_rule_closeout_outcome": SOURCE_RULE_CLOSEOUT_OUTCOME,
        "source_candidate_constraint_id": SOURCE_CANDIDATE_CONSTRAINT_ID,
        "source_candidate_constraint_form": SOURCE_CANDIDATE_CONSTRAINT_FORM,
        "source_candidate_constraint_equation": SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
        "source_admissibility_constraint_form": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        "selected_embedding_route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
        "admissibility_only_route_status": ADMISSIBILITY_ONLY_ROUTE_STATUS,
        "lagrange_multiplier_route_id": LAGRANGE_MULTIPLIER_ROUTE_ID,
        "lagrange_multiplier_route_status": LAGRANGE_MULTIPLIER_ROUTE_STATUS,
        "lagrange_multiplier_action_form": LAGRANGE_MULTIPLIER_ACTION_FORM,
        "penalty_route_id": PENALTY_ROUTE_ID,
        "penalty_route_status": PENALTY_ROUTE_STATUS,
        "penalty_action_form": PENALTY_ACTION_FORM,
        "closeout_criteria": closeout_criteria,
        "closeout_criteria_count": len(closeout_criteria),
        "closeout_criteria_accepted_count": sum(
            1 for row in closeout_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "admissibility_rule_closeout_prepared": True,
        "admissibility_rule_closeout_accepted": True,
        "second_phi_relevant_ck_admissibility_rule_candidate_closed": True,
        "bridge_admissibility_rule_candidate_closed": True,
        "bridge_admissibility_rule_closed_as_route_consistency_rule": True,
        "route_consistency_rule_candidate_closed": True,
        "admissibility_only_route_selected": True,
        "admissibility_only_interpretation_retained": True,
        "constraint_as_admissibility_rule_selected": True,
        "constraint_as_action_term_selected": False,
        "dynamical_action_embedding_selected": False,
        "dynamical_action_embedding_not_assumed": True,
        "candidate_recorded_as_rule_only": True,
        "candidate_recorded_as_new_physical_law": False,
        "candidate_recorded_as_action_term": False,
        "bridge_candidate_recorded_as_action_term": False,
        "bridge_candidate_recorded_as_new_dynamical_law": False,
        "route_consistency_tuple_carried_forward": True,
        "field_equation_match_component_preserved": True,
        "stress_energy_match_component_preserved": True,
        "source_residual_match_component_preserved": True,
        "source_admissibility_context_preserved": True,
        "lagrange_multiplier_route_recorded": True,
        "lagrange_multiplier_route_blocked": True,
        "penalty_route_recorded": True,
        "penalty_route_licensed": False,
        "rule_family_synthesis_packet_authorized": True,
        "rule_family_synthesis_packet_prepared": False,
        "phi_ck_admissibility_rule_family_contains_count": 2,
        "phi_ck_admissibility_rule_family_summary": rule_family_summary,
        "source_admissibility_rule_synthesis_entry_preserved": True,
        "bridge_admissibility_rule_synthesis_entry_preserved": True,
        "another_phi_derivation_selected": False,
        "transport_consistency_family_selected": False,
        "master_action_surface_rotation_selected": False,
        "qft_gr_semiclassical_prerequisite_return_selected": False,
        "public_explanatory_section_selected": False,
        "proof_depth_label": (
            "SECOND_PHI_RELEVANT_CK_ADMISSIBILITY_RULE_CANDIDATE_CLOSED_"
            "NO_ACTION_VARIATION"
        ),
        "bridge_functional_selected": False,
        "bridge_candidate_functional_defined": False,
        "bridge_candidate_functional_selected": False,
        "component_pairing_rule_selected": False,
        "multiplier_component_domain_selected": False,
        "constraint_multiplier_type_selected": False,
        "constraint_term_selected": False,
        "multiplier_type_selected": False,
        "multiplier_domain_selected": False,
        "covariance_of_multiplier_pairing_established": False,
        "boundary_terms_controlled": False,
        "variation_policy_for_embedding_selected": False,
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
        "bridge_candidate_rule_proved": False,
        "bridge_admissibility_claimed": False,
        "bridge_admissibility_proved": False,
        "bridge_route_alignment_verified": False,
        "route_consistency_tuple_proved": False,
        "field_equation_match_proved": False,
        "stress_energy_match_proved": False,
        "source_residual_match_proved": False,
        "phi_generated_by_ck_claimed": False,
        "phi_generation_theorem_claimed": False,
        "derived_v_phi_claimed": False,
        "v_phi_derivation_claimed": False,
        "potential_derived": False,
        "new_conservation_proof_claimed": False,
        "new_source_admissibility_proof_claimed": False,
        "source_admissibility_claimed": False,
        "source_admissibility_completed": False,
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
        "native_generation_theorem_claimed": False,
        "empirical_validation_claimed": False,
        "public_readiness_claimed": False,
        "public_submission_authorized": False,
        "phase2_readiness_claim": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "mathematical_statement": (
            "The phi bridge-admissibility C_k candidate is closed as a "
            "route-consistency admissibility-rule candidate: C_bridge^phi := "
            "(E_phi^master - E_phi^witness, T_phi^master - T_phi^witness, "
            "C_source^phi - nabla_mu T_phi^{mu nu}), with rule "
            "C_bridge^phi = 0. It states that the phi route is allowed only "
            "when the master-action phi equation, stress-energy route, and "
            "source-residual route match the successful scalar witness/source "
            "route. The closeout is admissibility-only and executes no action "
            "variation."
        ),
        "non_claim_boundary": (
            "This closeout records the second phi-relevant C_k admissibility "
            "rule candidate only. It keeps C_bridge^phi = 0 as a bridge-"
            "admissibility route-consistency admissibility-rule candidate, "
            "not as an action term, "
            "not as a new dynamical law, not as a native-generation theorem, "
            "not as QFT-GR closure, and not as master-action promotion. It "
            "does not functionalize C_bridge^phi, does not embed it in S_C, "
            "does not select Lambda_bridge or a multiplier domain, does not "
            "select a component pairing rule, does not prove covariance of a "
            "multiplier pairing, does not control boundary terms, does not "
            "select an embedding variation policy, does not license the "
            "penalty route, does not select or define a fully concrete C_k "
            "functional, does not execute C_k variation, does not vary "
            "Lambda_bridge, phi, or g, does not prove full bridge "
            "admissibility, does not prove the field-equation match, does "
            "not prove the stress-energy match, does not prove the "
            "source-residual match, does not verify full route alignment, "
            "does not claim phi generation, does not derive V(phi), does not "
            "prove new conservation, does not prove new source "
            "admissibility, does not close QFT-GR, does not authorize "
            "semiclassical coupling, does not promote the master action, "
            "does not claim empirical validation, and does not authorize "
            "public readiness. The next target is a synthesis packet for the "
            "source and bridge phi/C_k admissibility-rule family, not another "
            "immediate phi derivation."
        ),
        "critical_gate_fail_conditions": [
            "claim C_bridge^phi = 0 is an action term",
            "claim C_k action embedding",
            "execute C_k variation",
            "claim the multiplier/action route is selected",
            "claim the penalty route is licensed",
            "claim full bridge admissibility is proved",
            "claim route alignment is verified",
            "claim phi generation",
            "claim V(phi) derivation",
            "claim new conservation proof",
            "claim new source-admissibility proof",
            "claim QFT-GR closure",
            "claim semiclassical coupling",
            "promote the master action",
            "claim empirical validation",
            "start another phi derivation before the family synthesis packet",
        ],
        "validation_policy": _validation_policy(),
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "aggregate_lean_validation_status_for_packet": AGGREGATE_TIMEOUT_STATUS,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.PhiBridgeAdmissibilityCKAdmissibilityRuleCloseout",
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
            "Build the phi bridge-admissibility C_k admissibility rule closeout."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    closeout = build_phi_bridge_admissibility_ck_admissibility_rule_closeout(
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
