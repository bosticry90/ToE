from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_transport_consistency_ck_constraint_candidate_packet_result_review_report import (
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
    BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
    BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
    DEFAULT_OUT as CANDIDATE_REVIEW_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    KNOWN_PHI_TRANSPORT_CHAIN_FORM,
    KNOWN_PHI_TRANSPORT_CHAIN_STEPS,
    LEAN_VALIDATION_POLICY_ID,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as CANDIDATE_REVIEW_OUTCOME,
    PACKET_ID as CANDIDATE_REVIEW_PACKET_ID,
    REVIEW_RESULT as CANDIDATE_REVIEW_RESULT,
    SCHEMA_ID as CANDIDATE_REVIEW_SCHEMA_ID,
    SELECTED_CK_CONSTRAINT_FAMILY,
    SELECTED_CK_OPTION_CLASS,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
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

SCHEMA_ID = "PHI_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_PACKET_20260619_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "PHI_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_PACKET_v0"
PACKET_RESULT = (
    "PHI_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_OPTIONS_RECORDED_"
    "ADMISSIBILITY_ONLY_ROUTE_SELECTED_NO_ACTION_VARIATION"
)
OUTCOME_ID = (
    "PHI_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_PACKET_PREPARED_"
    + PACKET_RESULT
)
PACKET_CLASSIFICATION = (
    "phi_transport_consistency_ck_functional_embedding_packet_records_options_"
    "and_selects_admissibility_only_no_action_variation"
)
NEXT_TARGET = "review_phi_transport_consistency_ck_functional_embedding_packet_result"
NEXT_TARGET_KIND = "phi_transport_consistency_ck_functional_embedding_packet_result_review"

ADMISSIBILITY_ONLY_ROUTE_ID = "phi_transport_ck_admissibility_only_route"
TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM = "C_transport^phi = 0"
ADMISSIBILITY_ONLY_ROUTE_STATUS = (
    "selected_non_dynamical_derivation_chain_stability_rule"
)
LAGRANGE_MULTIPLIER_ROUTE_ID = "phi_transport_ck_lagrange_multiplier_action_route"
LAGRANGE_MULTIPLIER_ACTION_FORM = (
    "S_C^transport = integral_M dVol_g Lambda_transport dot C_transport^phi"
)
LAGRANGE_MULTIPLIER_ROUTE_STATUS = (
    "blocked_by_route_component_domain_pairing_covariance_boundary_regime_"
    "projection_and_variation_scope"
)
PENALTY_ROUTE_ID = "phi_transport_ck_penalty_route"
PENALTY_ACTION_FORM = "S_C^transport = integral_M dVol_g norm(C_transport^phi)^2"
PENALTY_ROUTE_STATUS = "recorded_not_licensed"
DIRECT_DYNAMICAL_LAW_INTERPRETATION_ID = (
    "phi_transport_ck_direct_dynamical_law_interpretation"
)
DIRECT_DYNAMICAL_LAW_INTERPRETATION_STATUS = "recorded_blocked_not_selected"

TRANSPORT_ACTION_EMBEDDING_CHAIN_FORM = (
    "ACTION -> VARIATION -> BRIDGE -> OPERATOR -> TRANSPORT -> "
    "RESIDUAL_LAW -> REGIME_LIMIT"
)
TRANSPORT_MULTIPLIER_BLOCKING_REASONS = [
    "missing multiplier type",
    "missing component pairing rule",
    "missing transport-map domains/codomains",
    "missing covariance rule",
    "missing boundary/regime projection control",
    "missing embedding variation policy",
]
TRANSPORT_PENALTY_BLOCKING_REASONS = [
    "norm over heterogeneous route-consistency tuple not defined",
    "penalty term would change the dynamics",
    "transport component metric/regularity weights not selected",
    "boundary/regime projection control not established",
]
DIRECT_DYNAMICAL_LAW_BLOCKING_REASONS = [
    "C_transport^phi is an admissibility rule candidate",
    "no transport evolution operator is defined",
    "no dynamical variation policy is selected",
    "no transport proof or full route-alignment proof is available",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_PACKET_"
    "20260619_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiTransportConsistencyCKFunctionalEmbeddingPacket.lean"
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


def _embedding_routes() -> list[dict[str, Any]]:
    return [
        {
            "route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
            "route_type": "admissibility_only_derivation_chain_stability_rule",
            "status": ADMISSIBILITY_ONLY_ROUTE_STATUS,
            "constraint_form": TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
            "plain_meaning": (
                "The phi route is admitted only if transported equation, "
                "source, conservation-residual, and regime-facing objects "
                "remain compatible through the derivation chain."
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
            "blocking_reasons": TRANSPORT_MULTIPLIER_BLOCKING_REASONS,
            "action_term_selected": False,
            "action_variation_executed": False,
            "selected_for_current_packet": False,
        },
        {
            "route_id": PENALTY_ROUTE_ID,
            "route_type": "quadratic_or_norm_penalty_embedding",
            "status": PENALTY_ROUTE_STATUS,
            "action_form": PENALTY_ACTION_FORM,
            "blocking_reasons": TRANSPORT_PENALTY_BLOCKING_REASONS,
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
            "assessment": "The transport candidate review authorized this packet.",
        },
        {
            "row_id": "transport_constraint_carried_forward",
            "status": "accepted",
            "evidence": TRANSPORT_CONSTRAINT_EQUATION,
            "assessment": "The condition C_transport^phi = 0 is preserved.",
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
            "assessment": (
                "The transport components are preserved as unproved route checks."
            ),
        },
        {
            "row_id": "source_and_bridge_context_preserved",
            "status": "accepted",
            "evidence": [
                SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
                BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
            ],
            "assessment": "The closed source and bridge rules remain context.",
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
            "evidence": TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
            "assessment": "Only the non-dynamical route-stability rule is selected.",
        },
        {
            "row_id": "multiplier_action_route_blocked",
            "status": "accepted",
            "evidence": LAGRANGE_MULTIPLIER_ACTION_FORM,
            "assessment": (
                "The multiplier/action route is blocked by missing type, "
                "pairing, domains/codomains, covariance, boundary/regime "
                "projection, and variation policy."
            ),
        },
        {
            "row_id": "penalty_route_not_licensed",
            "status": "accepted",
            "evidence": PENALTY_ACTION_FORM,
            "assessment": (
                "The penalty route is recorded but not licensed because no "
                "norm over the heterogeneous route tuple is defined."
            ),
        },
        {
            "row_id": "direct_dynamical_law_interpretation_blocked",
            "status": "accepted",
            "evidence": DIRECT_DYNAMICAL_LAW_INTERPRETATION_ID,
            "assessment": (
                "The direct dynamical-law interpretation is blocked; "
                "C_transport^phi remains admissibility-only."
            ),
        },
        {
            "row_id": "no_action_variation_executed",
            "status": "accepted",
            "evidence": [
                "ck_variation_executed=false",
                "lambda_variation_executed=false",
                "phi_variation_of_candidate_executed=false",
                "metric_variation_of_candidate_executed=false",
            ],
            "assessment": "No action variation is executed in this packet.",
        },
        {
            "row_id": "no_transport_proof_generation_closure_or_promotion",
            "status": "accepted",
            "evidence": [
                "transport_consistency_proved=false",
                "native_phi_derivation_claimed=false",
                "qft_gr_closure_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": "No transport proof, generation, closure, or promotion is claimed.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "phi_transport_consistency_ck_functional_embedding_packet",
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


def build_phi_transport_consistency_ck_functional_embedding_packet(
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
        "transport_candidate_exact": (
            candidate_review.get("transport_candidate_id") == TRANSPORT_CANDIDATE_ID
            and candidate_review.get("transport_candidate_type")
            == TRANSPORT_CANDIDATE_TYPE
            and candidate_review.get("transport_rule_classification")
            == TRANSPORT_RULE_CLASSIFICATION
            and candidate_review.get("transport_rule_epistemic_status")
            == TRANSPORT_RULE_EPISTEMIC_STATUS
            and candidate_review.get("transport_constraint_form")
            == TRANSPORT_CONSTRAINT_FORM
            and candidate_review.get("transport_constraint_equation")
            == TRANSPORT_CONSTRAINT_EQUATION
        ),
        "transport_components_exact_unproved": (
            candidate_review.get("transport_component_count") == len(TRANSPORT_COMPONENTS)
            and candidate_review.get("transport_components_preserved") is True
            and candidate_review.get("transport_components_proved") is False
            and candidate_review.get("transport_component_forms")
            == [row["component_form"] for row in TRANSPORT_COMPONENTS]
        ),
        "source_bridge_context_exact": (
            candidate_review.get("source_candidate_constraint_id")
            == SOURCE_CANDIDATE_CONSTRAINT_ID
            and candidate_review.get("source_candidate_constraint_form")
            == SOURCE_CANDIDATE_CONSTRAINT_FORM
            and candidate_review.get("source_candidate_constraint_equation")
            == SOURCE_CANDIDATE_CONSTRAINT_EQUATION
            and candidate_review.get("source_admissibility_constraint_form")
            == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
            and candidate_review.get("bridge_constraint_form") == BRIDGE_CONSTRAINT_FORM
            and candidate_review.get("bridge_constraint_equation")
            == BRIDGE_CONSTRAINT_EQUATION
            and candidate_review.get("bridge_admissibility_constraint_form")
            == BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "known_transport_chain_exact": (
            candidate_review.get("known_phi_transport_chain_form")
            == KNOWN_PHI_TRANSPORT_CHAIN_FORM
            and candidate_review.get("known_phi_transport_chain_steps")
            == KNOWN_PHI_TRANSPORT_CHAIN_STEPS
        ),
        "three_routes_recorded": len(routes) == 3,
        "admissibility_only_selected": (
            routes[0]["route_id"] == ADMISSIBILITY_ONLY_ROUTE_ID
            and routes[0]["selected_for_current_packet"] is True
            and routes[0]["action_term_selected"] is False
        ),
        "action_routes_not_licensed": all(
            route["action_term_selected"] is False
            and route["action_variation_executed"] is False
            for route in routes
        ),
        "multiplier_route_blocked": (
            routes[1]["status"] == LAGRANGE_MULTIPLIER_ROUTE_STATUS
            and routes[1]["blocking_reasons"] == TRANSPORT_MULTIPLIER_BLOCKING_REASONS
        ),
        "penalty_route_not_licensed": (
            routes[2]["status"] == PENALTY_ROUTE_STATUS
            and routes[2]["blocking_reasons"] == TRANSPORT_PENALTY_BLOCKING_REASONS
        ),
        "direct_dynamical_law_blocked": (
            DIRECT_DYNAMICAL_LAW_INTERPRETATION_STATUS
            == "recorded_blocked_not_selected"
        ),
        "review_rows_all_accepted": all(
            row["status"] == "accepted" for row in review_rows
        ),
        "aggregate_recorded_not_run": (
            FULL_TOEFORMAL_AGGREGATE_STATUS == "NOT_RUN"
        ),
        "next_review_target_selected": (
            NEXT_TARGET
            == "review_phi_transport_consistency_ck_functional_embedding_packet_result"
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_PHI_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_PACKET"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_PHI_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PHI_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_PACKET_REQUIRES_REMEDIATION",
        "packet_result": PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "candidate_review_outcome": CANDIDATE_REVIEW_OUTCOME,
        "candidate_review_result": CANDIDATE_REVIEW_RESULT,
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
        "bridge_route_field_equation_match": BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
        "bridge_route_stress_energy_match": BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
        "bridge_route_source_residual_match": BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
        "closed_phi_ck_rule_roles": [
            "source admissibility",
            "bridge admissibility",
            "transport consistency",
        ],
        "closed_phi_ck_rule_roles_plain": (
            "source admissibility -> bridge admissibility -> transport consistency"
        ),
        "phi_ck_rule_family_count_after_packet": 3,
        "embedding_routes": routes,
        "embedding_route_count": len(routes),
        "selected_embedding_route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
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
        "lagrange_multiplier_action_form": LAGRANGE_MULTIPLIER_ACTION_FORM,
        "transport_multiplier_blocking_reasons": TRANSPORT_MULTIPLIER_BLOCKING_REASONS,
        "missing_multiplier_type": True,
        "component_pairing_rule_missing": True,
        "transport_map_domains_codomains_missing": True,
        "covariance_rule_missing": True,
        "boundary_regime_projection_control_missing": True,
        "embedding_variation_policy_missing": True,
        "penalty_route_recorded": True,
        "penalty_route_licensed": False,
        "penalty_action_form": PENALTY_ACTION_FORM,
        "transport_penalty_blocking_reasons": TRANSPORT_PENALTY_BLOCKING_REASONS,
        "heterogeneous_tuple_norm_defined": False,
        "penalty_would_change_dynamics": True,
        "direct_dynamical_law_interpretation_recorded": True,
        "direct_dynamical_law_interpretation_blocked": True,
        "direct_dynamical_law_interpretation_selected": False,
        "direct_dynamical_law_interpretation_id": (
            DIRECT_DYNAMICAL_LAW_INTERPRETATION_ID
        ),
        "direct_dynamical_law_blocking_reasons": DIRECT_DYNAMICAL_LAW_BLOCKING_REASONS,
        "dynamical_action_embedding_selected": False,
        "dynamical_action_embedding_not_assumed": True,
        "constraint_as_action_term_selected": False,
        "transport_candidate_recorded_as_action_term": False,
        "transport_candidate_recorded_as_new_dynamical_law": False,
        "transport_functional_selected": False,
        "transport_candidate_functional_defined": False,
        "transport_candidate_functional_selected": False,
        "fully_concrete_ck_functional_selected": False,
        "fully_concrete_ck_functional_defined": False,
        "concrete_ck_functional_selected": False,
        "concrete_ck_functional_defined": False,
        "ck_functional_formula_fully_defined": False,
        "ck_functional_formula_selected": False,
        "ck_action_embedding_claimed": False,
        "candidate_action_insertion_executed": False,
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
        "review_rows": review_rows,
        "review_row_count": len(review_rows),
        "review_row_accepted_count": sum(
            1 for row in review_rows if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "proof_depth_label": (
            "PHI_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_OPTIONS_"
            "RECORDED_ADMISSIBILITY_ONLY"
        ),
        "mathematical_statement": (
            "The functional-embedding packet records three routes for the phi "
            "transport-consistency C_k candidate. The admissibility-only route "
            "C_transport^phi = 0 is selected as a non-dynamical "
            "derivation-chain stability rule. The multiplier/action route "
            "S_C^transport = integral_M dVol_g Lambda_transport dot "
            "C_transport^phi is blocked because C_transport^phi is a "
            "route-level object over multiple stages and lacks multiplier "
            "type, component pairing, transport-map domains/codomains, "
            "covariance, boundary/regime projection control, and embedding "
            "variation policy. The penalty route S_C^transport = integral_M "
            "dVol_g norm(C_transport^phi)^2 is recorded but not licensed. "
            "No action variation is executed."
        ),
        "non_claim_boundary": (
            "This packet records transport functional-embedding options and "
            "selects the admissibility-only route. It does not functionalize "
            "C_transport^phi, does not embed it in S_C, does not define a C_k "
            "action term, does not select Lambda_transport or any multiplier "
            "type, does not select a component pairing rule, does not select "
            "transport-map domains/codomains, does not prove covariance of "
            "the multiplier pairing, does not control boundary or regime "
            "projection terms, does not select an embedding variation policy, "
            "does not license the penalty route, does not define a norm over "
            "the heterogeneous transport tuple, does not interpret the "
            "candidate as a direct dynamical law, does not select or define a "
            "fully concrete C_k functional, does not execute C_k variation, "
            "does not vary Lambda_transport, phi, or g, does not prove "
            "transport consistency, does not prove full route alignment, does "
            "not prove any transport component, does not generate phi, does "
            "not derive V(phi), does not prove new conservation, does not "
            "prove source admissibility, does not close QFT-GR, does not "
            "authorize semiclassical coupling, does not promote the master "
            "action, does not claim empirical validation, and does not "
            "authorize public readiness. The full ToeFormal aggregate is "
            "recorded as NOT_RUN for this packet."
        ),
        "critical_gate_fail_conditions": [
            "claim the multiplier route is selected as an action term",
            "claim the penalty route is licensed",
            "claim the direct dynamical-law interpretation is selected",
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
            "ToeFormal.Derivation.PhiTransportConsistencyCKFunctionalEmbeddingPacket",
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
            "Build the phi transport-consistency C_k functional embedding packet."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    packet = build_phi_transport_consistency_ck_functional_embedding_packet(
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
