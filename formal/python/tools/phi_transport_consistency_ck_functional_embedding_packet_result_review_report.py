from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_transport_consistency_ck_functional_embedding_packet_report import (
    ADMISSIBILITY_ONLY_ROUTE_ID,
    ADMISSIBILITY_ONLY_ROUTE_STATUS,
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    DEFAULT_OUT as EMBEDDING_PACKET_PATH,
    DIRECT_DYNAMICAL_LAW_BLOCKING_REASONS,
    DIRECT_DYNAMICAL_LAW_INTERPRETATION_ID,
    DIRECT_DYNAMICAL_LAW_INTERPRETATION_STATUS,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    KNOWN_PHI_TRANSPORT_CHAIN_FORM,
    KNOWN_PHI_TRANSPORT_CHAIN_STEPS,
    LAGRANGE_MULTIPLIER_ACTION_FORM,
    LAGRANGE_MULTIPLIER_ROUTE_ID,
    LAGRANGE_MULTIPLIER_ROUTE_STATUS,
    LEAN_VALIDATION_POLICY_ID,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as EMBEDDING_PACKET_OUTCOME,
    PACKET_ID as EMBEDDING_PACKET_ID,
    PACKET_RESULT as EMBEDDING_PACKET_RESULT,
    PENALTY_ACTION_FORM,
    PENALTY_ROUTE_ID,
    PENALTY_ROUTE_STATUS,
    SCHEMA_ID as EMBEDDING_PACKET_SCHEMA_ID,
    SELECTED_CK_CONSTRAINT_FAMILY,
    SELECTED_CK_OPTION_CLASS,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
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
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-19T00:00:00Z"

SCHEMA_ID = (
    "PHI_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW_"
    "20260619_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "PHI_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW_v0"
REVIEW_RESULT = (
    "PHI_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_RESULT_REVIEW_ACCEPTS_"
    "ADMISSIBILITY_ONLY_ROUTE_NO_ACTION_VARIATION_OR_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "phi_transport_consistency_ck_functional_embedding_result_review_accepts_"
    "admissibility_only_route_no_action_variation_or_promotion"
)
NEXT_TARGET = "prepare_phi_transport_consistency_ck_admissibility_rule_closeout"
NEXT_TARGET_KIND = "phi_transport_consistency_ck_admissibility_rule_closeout_preparation"
THIRD_RULE_CLASSIFICATION = "third_phi_relevant_ck_admissibility_rule_candidate"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW_"
    "20260619_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiTransportConsistencyCKFunctionalEmbeddingPacketResultReview.lean"
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


def _review_criteria(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "admissibility_only_route_selected",
            "status": "accepted",
            "evidence": packet.get("transport_admissibility_constraint_form"),
            "assessment": (
                "The review accepts only C_transport^phi = 0 as a "
                "non-dynamical derivation-chain stability rule."
            ),
        },
        {
            "row_id": "c_transport_zero_preserved_as_rule",
            "status": "accepted",
            "evidence": TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
            "assessment": (
                "C_transport^phi = 0 is preserved as an admissibility rule "
                "rather than an action term."
            ),
        },
        {
            "row_id": "transport_tuple_carried_forward",
            "status": "accepted",
            "evidence": TRANSPORT_CONSTRAINT_FORM,
            "assessment": "The derivation-chain stability tuple is carried forward.",
        },
        {
            "row_id": "transport_components_carried_forward",
            "status": "accepted",
            "evidence": [row["component_form"] for row in TRANSPORT_COMPONENTS],
            "assessment": "The five transport components are preserved unproved.",
        },
        {
            "row_id": "source_and_bridge_context_preserved",
            "status": "accepted",
            "evidence": [
                SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
                BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
            ],
            "assessment": "The source and bridge admissibility rules remain context.",
        },
        {
            "row_id": "multiplier_action_route_blocked",
            "status": "accepted",
            "evidence": LAGRANGE_MULTIPLIER_ACTION_FORM,
            "assessment": (
                "The multiplier/action route remains blocked by missing type, "
                "pairing, transport-map domains/codomains, covariance, "
                "boundary/regime projection control, and variation policy."
            ),
        },
        {
            "row_id": "penalty_route_not_licensed",
            "status": "accepted",
            "evidence": PENALTY_ACTION_FORM,
            "assessment": "The penalty route is recorded but not licensed.",
        },
        {
            "row_id": "direct_dynamical_law_interpretation_blocked",
            "status": "accepted",
            "evidence": DIRECT_DYNAMICAL_LAW_INTERPRETATION_ID,
            "assessment": (
                "The direct dynamical-law interpretation remains blocked; "
                "C_transport^phi remains admissibility-only."
            ),
        },
        {
            "row_id": "no_ck_variation_or_action_embedding",
            "status": "accepted",
            "evidence": [
                "ck_variation_executed=false",
                "lambda_variation_executed=false",
                "phi_variation_of_candidate_executed=false",
                "metric_variation_of_candidate_executed=false",
            ],
            "assessment": "No C_k, multiplier, phi, metric, or penalty variation is executed.",
        },
        {
            "row_id": "no_transport_proof_or_route_alignment_proof",
            "status": "accepted",
            "evidence": [
                "transport_consistency_proved=false",
                "full_route_alignment_proved=false",
                "route_chain_compatibility_proved=false",
            ],
            "assessment": (
                "The review accepts the admissibility-only route without "
                "claiming transport consistency or full route alignment."
            ),
        },
        {
            "row_id": "no_phi_generation_or_potential_derivation",
            "status": "accepted",
            "evidence": [
                "phi_generated_by_ck_claimed=false",
                "phi_generation_theorem_claimed=false",
                "potential_derived=false",
            ],
            "assessment": "The review claims neither phi generation nor V(phi) derivation.",
        },
        {
            "row_id": "no_qft_gr_closure_or_master_action_promotion",
            "status": "accepted",
            "evidence": [
                "qft_gr_closure_claimed=false",
                "semiclassical_coupling_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": (
                "QFT-GR closure, semiclassical coupling, and master-action "
                "promotion remain blocked."
            ),
        },
        {
            "row_id": "full_toeformal_aggregate_recorded_not_run",
            "status": "accepted",
            "evidence": FULL_TOEFORMAL_AGGREGATE_STATUS,
            "assessment": "The full ToeFormal aggregate remains recorded as NOT_RUN.",
        },
        {
            "row_id": "transport_admissibility_rule_closeout_next_target_selected",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": (
                "The next target is a bounded closeout of the third "
                "phi-relevant C_k admissibility rule candidate."
            ),
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "phi_transport_consistency_ck_functional_embedding_packet_result_review"
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


def build_phi_transport_consistency_ck_functional_embedding_packet_result_review(
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
        "transport_rule_preserved": (
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
        "admissibility_only_route_selected": (
            packet.get("admissibility_only_route_selected") is True
            and packet.get("constraint_as_admissibility_rule_selected") is True
            and packet.get("constraint_as_action_term_selected") is False
            and packet.get("selected_embedding_route_id") == ADMISSIBILITY_ONLY_ROUTE_ID
        ),
        "action_routes_blocked_or_unlicensed": (
            packet.get("lagrange_multiplier_route_blocked") is True
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
        "source_bridge_context_exact": (
            packet.get("source_candidate_constraint_id")
            == SOURCE_CANDIDATE_CONSTRAINT_ID
            and packet.get("source_candidate_constraint_form")
            == SOURCE_CANDIDATE_CONSTRAINT_FORM
            and packet.get("source_candidate_constraint_equation")
            == SOURCE_CANDIDATE_CONSTRAINT_EQUATION
            and packet.get("source_admissibility_constraint_form")
            == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
            and packet.get("bridge_constraint_form") == BRIDGE_CONSTRAINT_FORM
            and packet.get("bridge_constraint_equation")
            == BRIDGE_CONSTRAINT_EQUATION
            and packet.get("bridge_admissibility_constraint_form")
            == BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "transport_chain_exact": (
            packet.get("transport_action_embedding_chain_form")
            == TRANSPORT_ACTION_EMBEDDING_CHAIN_FORM
            and packet.get("known_phi_transport_chain_form")
            == KNOWN_PHI_TRANSPORT_CHAIN_FORM
            and packet.get("known_phi_transport_chain_steps")
            == KNOWN_PHI_TRANSPORT_CHAIN_STEPS
        ),
        "no_action_embedding_or_variation": all(
            packet.get(key) is False
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
            packet.get(key) is False
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
                "native_generation_theorem_claimed",
                "empirical_validation_claimed",
                "public_readiness_claimed",
                "phase2_readiness_claim",
                "pillar_completion_inferred",
                "seam_closure_claim",
            ]
        ),
        "aggregate_recorded_not_run": (
            packet.get("full_toeformal_aggregate_status_for_packet")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
            and packet.get("aggregate_lean_validation_status_for_packet")
            == FULL_TOEFORMAL_AGGREGATE_STATUS
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
        else "REMEDIATE_PHI_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_REVIEW"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PHI_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_PACKET_"
            "RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "review_prepared": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PHI_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_REVIEW_REQUIRES_REMEDIATION",
        "review_result": REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "embedding_packet_outcome": EMBEDDING_PACKET_OUTCOME,
        "embedding_packet_result": EMBEDDING_PACKET_RESULT,
        "selected_ck_option_class": SELECTED_CK_OPTION_CLASS,
        "selected_ck_constraint_family": SELECTED_CK_CONSTRAINT_FAMILY,
        "transport_candidate_id": TRANSPORT_CANDIDATE_ID,
        "transport_candidate_type": TRANSPORT_CANDIDATE_TYPE,
        "transport_rule_classification": TRANSPORT_RULE_CLASSIFICATION,
        "transport_rule_epistemic_status": TRANSPORT_RULE_EPISTEMIC_STATUS,
        "transport_constraint_form": TRANSPORT_CONSTRAINT_FORM,
        "transport_constraint_equation": TRANSPORT_CONSTRAINT_EQUATION,
        "transport_admissibility_constraint_form": TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
        "transport_component_count": len(TRANSPORT_COMPONENTS),
        "transport_component_forms": [row["component_form"] for row in TRANSPORT_COMPONENTS],
        "transport_components_preserved": True,
        "transport_components_proved": False,
        "transport_action_embedding_chain_form": TRANSPORT_ACTION_EMBEDDING_CHAIN_FORM,
        "known_phi_transport_chain_form": KNOWN_PHI_TRANSPORT_CHAIN_FORM,
        "known_phi_transport_chain_steps": KNOWN_PHI_TRANSPORT_CHAIN_STEPS,
        "source_candidate_constraint_id": SOURCE_CANDIDATE_CONSTRAINT_ID,
        "source_candidate_constraint_form": SOURCE_CANDIDATE_CONSTRAINT_FORM,
        "source_candidate_constraint_equation": SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
        "source_admissibility_constraint_form": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        "bridge_constraint_form": BRIDGE_CONSTRAINT_FORM,
        "bridge_constraint_equation": BRIDGE_CONSTRAINT_EQUATION,
        "bridge_admissibility_constraint_form": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        "closed_phi_ck_rule_roles": [
            "source admissibility",
            "bridge admissibility",
            "transport consistency",
        ],
        "closed_phi_ck_rule_roles_plain": (
            "source admissibility -> bridge admissibility -> transport consistency"
        ),
        "embedding_route_count": 3,
        "selected_embedding_route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
        "admissibility_only_route_status": ADMISSIBILITY_ONLY_ROUTE_STATUS,
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
        "transport_multiplier_blocking_reasons": TRANSPORT_MULTIPLIER_BLOCKING_REASONS,
        "transport_penalty_blocking_reasons": TRANSPORT_PENALTY_BLOCKING_REASONS,
        "direct_dynamical_law_blocking_reasons": DIRECT_DYNAMICAL_LAW_BLOCKING_REASONS,
        "functional_embedding_result_review_prepared": True,
        "functional_embedding_result_review_accepted": True,
        "review_accepts_admissibility_only_route": True,
        "packet_result_review_accepts_admissibility_only_route": True,
        "transport_admissibility_rule_closeout_authorized": True,
        "transport_admissibility_rule_closeout_prepared": False,
        "third_phi_relevant_ck_admissibility_rule_candidate_classification": (
            THIRD_RULE_CLASSIFICATION
        ),
        "functional_embedding_packet_prepared": True,
        "functional_embedding_options_recorded": True,
        "admissibility_only_route_selected": True,
        "admissibility_only_interpretation_retained": True,
        "constraint_as_admissibility_rule_selected": True,
        "transport_constraint_carried_forward": True,
        "transport_tuple_carried_forward": True,
        "transport_components_carried_forward": True,
        "source_and_bridge_context_preserved": True,
        "known_phi_chain_preserved": True,
        "lagrange_multiplier_route_recorded": True,
        "lagrange_multiplier_route_blocked": True,
        "penalty_route_recorded": True,
        "penalty_route_licensed": False,
        "direct_dynamical_law_interpretation_recorded": True,
        "direct_dynamical_law_interpretation_blocked": True,
        "direct_dynamical_law_interpretation_selected": False,
        "dynamical_action_embedding_selected": False,
        "dynamical_action_embedding_not_assumed": True,
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
        "penalty_would_change_dynamics": True,
        "fully_concrete_ck_functional_selected": False,
        "fully_concrete_ck_functional_defined": False,
        "concrete_ck_functional_selected": False,
        "concrete_ck_functional_defined": False,
        "ck_functional_formula_fully_defined": False,
        "ck_functional_formula_selected": False,
        "ck_action_embedding_claimed": False,
        "candidate_action_insertion_executed": False,
        "ck_variation_executed": False,
        "ck_variation_authorized": False,
        "lambda_variation_executed": False,
        "metric_variation_of_candidate_executed": False,
        "phi_variation_of_candidate_executed": False,
        "penalty_variation_executed": False,
        "transport_candidate_rule_proved": False,
        "transport_consistency_claimed": False,
        "transport_consistency_proved": False,
        "transport_proof_claimed": False,
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
        "review_criteria": criteria,
        "review_criteria_count": len(criteria),
        "review_criteria_accepted_count": sum(
            1 for row in criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "proof_depth_label": (
            "PHI_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_REVIEW_"
            "ACCEPTS_ADMISSIBILITY_ONLY"
        ),
        "mathematical_statement": (
            "The review accepts the transport functional-embedding packet only "
            "at the admissibility-rule level. The rule C_transport^phi = 0 is "
            "preserved as a non-dynamical derivation-chain stability condition. "
            "The multiplier/action route remains blocked, the penalty route "
            "remains not licensed, the direct dynamical-law interpretation "
            "remains blocked, and no action variation, transport proof, or "
            "promotion is executed."
        ),
        "non_claim_boundary": (
            "This review accepts the admissibility-only route as a transport "
            "derivation-chain stability rule only, not as an action term. It "
            "preserves C_transport^phi = 0 as an admissibility rule, keeps the "
            "multiplier/action route blocked by missing multiplier type, "
            "component pairing rule, transport-map domains/codomains, "
            "covariance rule, boundary/regime projection control, and "
            "embedding variation policy, keeps the penalty route not licensed, "
            "and keeps direct dynamical-law interpretation blocked. It does "
            "not functionalize C_transport^phi, does not embed it in S_C, "
            "does not define a C_k action term, does not select "
            "Lambda_transport or any multiplier type, does not select "
            "transport-map domains/codomains, does not define a norm over the "
            "heterogeneous transport tuple, does not execute C_k variation, "
            "does not vary Lambda_transport, does not vary the candidate with "
            "respect to phi or g, does not prove transport consistency, does "
            "not prove full route alignment, does not prove any transport "
            "component, does not claim phi generation, does not derive V(phi), "
            "does not prove new conservation, does not prove source "
            "admissibility, does not close QFT-GR, does not authorize "
            "semiclassical coupling, does not promote the master action, does "
            "not claim empirical validation, and does not authorize public "
            "readiness. The full ToeFormal aggregate is recorded as NOT_RUN "
            "for this review."
        ),
        "critical_gate_fail_conditions": [
            "treat C_transport^phi = 0 as a selected dynamical action term",
            "claim the multiplier/action route is selected",
            "claim the penalty route is licensed",
            "claim direct dynamical-law interpretation is selected",
            "select Lambda_transport or a multiplier type",
            "select a component pairing rule",
            "select transport-map domains/codomains",
            "claim covariance of the multiplier pairing is established",
            "claim boundary or regime projection terms are controlled",
            "select an embedding variation policy",
            "execute C_k or Lambda_transport variation",
            "execute phi or metric variation of the candidate",
            "claim a norm over C_transport^phi is defined",
            "claim transport consistency is proved",
            "claim full route alignment is proved",
            "claim any transport component is proved",
            "claim phi is generated by C_k",
            "claim V(phi) is derived",
            "claim source admissibility or conservation newly proved",
            "claim QFT-GR closure",
            "claim semiclassical coupling",
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
            "ToeFormal.Derivation.PhiTransportConsistencyCKFunctionalEmbeddingPacketResultReview",
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
            "Build the phi transport-consistency C_k functional-embedding "
            "packet result review."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    review = (
        build_phi_transport_consistency_ck_functional_embedding_packet_result_review(
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
