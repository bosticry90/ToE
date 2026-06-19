from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_bridge_admissibility_ck_constraint_candidate_packet_result_review_report import (
    AGGREGATE_TIMEOUT_STATUS,
    BRIDGE_CANDIDATE_ID,
    BRIDGE_CANDIDATE_RULE_PLAIN_MEANING,
    BRIDGE_CANDIDATE_TYPE,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    BRIDGE_ROUTE_ALIGNMENT_SEQUENCE,
    BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
    BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
    BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
    DEFAULT_OUT as CANDIDATE_REVIEW_PATH,
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
    SOURCE_RULE_CLOSEOUT_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-18T00:00:00Z"

SCHEMA_ID = "PHI_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_20260618_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "PHI_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_v0"
PACKET_RESULT = (
    "PHI_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_OPTIONS_RECORDED_"
    "ADMISSIBILITY_ONLY_ROUTE_SELECTED_NO_ACTION_VARIATION"
)
OUTCOME_ID = (
    "PHI_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_PREPARED_"
    + PACKET_RESULT
)
PACKET_CLASSIFICATION = (
    "phi_bridge_admissibility_ck_functional_embedding_packet_records_options_"
    "and_selects_admissibility_only_no_action_variation"
)
NEXT_TARGET = "review_phi_bridge_admissibility_ck_functional_embedding_packet_result"
NEXT_TARGET_KIND = "phi_bridge_admissibility_ck_functional_embedding_packet_result_review"
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"

ADMISSIBILITY_ONLY_ROUTE_ID = "phi_bridge_ck_admissibility_only_route"
BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM = "C_bridge^phi = 0"
ADMISSIBILITY_ONLY_ROUTE_STATUS = "selected_non_dynamical_route_consistency_rule"
LAGRANGE_MULTIPLIER_ROUTE_ID = "phi_bridge_ck_lagrange_multiplier_action_route"
LAGRANGE_MULTIPLIER_ACTION_FORM = (
    "S_C^bridge = integral_M dVol_g Lambda_bridge dot C_bridge^phi"
)
LAGRANGE_MULTIPLIER_ROUTE_STATUS = (
    "blocked_by_multiplier_component_pairing_domain_covariance_boundary_"
    "and_variation_scope"
)
PENALTY_ROUTE_ID = "phi_bridge_ck_penalty_route"
PENALTY_ACTION_FORM = "S_C^bridge = integral_M dVol_g norm(C_bridge^phi)^2"
PENALTY_ROUTE_STATUS = "recorded_not_licensed"
COMPONENT_PAIRING_REQUIREMENTS = [
    "multiplier type for equation-match component",
    "multiplier type for stress-energy-match component",
    "multiplier type for source-residual-match component",
    "component pairing rule",
    "codomain/domain for each bridge component",
    "covariance rule for the paired tuple",
    "boundary control",
    "variation policy",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_20260618_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiBridgeAdmissibilityCKFunctionalEmbeddingPacket.lean"
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
            "route_type": "admissibility_only_route_consistency_rule",
            "status": ADMISSIBILITY_ONLY_ROUTE_STATUS,
            "constraint_form": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
            "plain_meaning": (
                "The phi route is accepted only if the equation, "
                "stress-energy, and source-residual matches hold."
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
            "blocking_reasons": COMPONENT_PAIRING_REQUIREMENTS,
            "action_term_selected": False,
            "action_variation_executed": False,
            "selected_for_current_packet": False,
        },
        {
            "route_id": PENALTY_ROUTE_ID,
            "route_type": "quadratic_or_norm_penalty_embedding",
            "status": PENALTY_ROUTE_STATUS,
            "action_form": PENALTY_ACTION_FORM,
            "blocking_reasons": [
                "would turn a bridge-checking rule into a dynamical penalty",
                "requires a norm for a mixed equation/stress-energy/source tuple",
                "requires metric, regularity, and derivative-order control",
            ],
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
            "assessment": "The bridge candidate review authorized this packet.",
        },
        {
            "row_id": "bridge_tuple_carried_forward",
            "status": "accepted",
            "evidence": BRIDGE_CONSTRAINT_FORM,
            "assessment": "The route-consistency tuple is carried forward exactly.",
        },
        {
            "row_id": "bridge_condition_carried_forward",
            "status": "accepted",
            "evidence": BRIDGE_CONSTRAINT_EQUATION,
            "assessment": "The condition C_bridge^phi = 0 is preserved.",
        },
        {
            "row_id": "bridge_components_carried_forward",
            "status": "accepted",
            "evidence": [
                BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
                BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
                BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
            ],
            "assessment": (
                "The field-equation, stress-energy, and source-residual "
                "match components are preserved."
            ),
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
            "evidence": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
            "assessment": "Only the non-dynamical route-consistency rule is selected.",
        },
        {
            "row_id": "lagrange_multiplier_route_blocked",
            "status": "accepted",
            "evidence": LAGRANGE_MULTIPLIER_ACTION_FORM,
            "assessment": (
                "The multiplier route is blocked by component pairing, "
                "domain, covariance, boundary, and variation scope."
            ),
        },
        {
            "row_id": "penalty_route_not_licensed",
            "status": "accepted",
            "evidence": PENALTY_ACTION_FORM,
            "assessment": "The penalty route is recorded but not licensed.",
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
            "row_id": "no_bridge_proof_generation_closure_or_promotion",
            "status": "accepted",
            "evidence": [
                "bridge_admissibility_proved=false",
                "phi_generated_by_ck_claimed=false",
                "qft_gr_closure_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": "No bridge proof, generation, closure, or promotion is claimed.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "phi_bridge_admissibility_ck_functional_embedding_packet",
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


def build_phi_bridge_admissibility_ck_functional_embedding_packet(
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
        "bridge_tuple_exact": (
            candidate_review.get("bridge_candidate_id") == BRIDGE_CANDIDATE_ID
            and candidate_review.get("bridge_candidate_type") == BRIDGE_CANDIDATE_TYPE
            and candidate_review.get("bridge_constraint_form") == BRIDGE_CONSTRAINT_FORM
            and candidate_review.get("bridge_constraint_equation")
            == BRIDGE_CONSTRAINT_EQUATION
        ),
        "bridge_components_exact": (
            candidate_review.get("bridge_route_field_equation_match")
            == BRIDGE_ROUTE_FIELD_EQUATION_MATCH
            and candidate_review.get("bridge_route_stress_energy_match")
            == BRIDGE_ROUTE_STRESS_ENERGY_MATCH
            and candidate_review.get("bridge_route_source_residual_match")
            == BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH
        ),
        "selected_family_exact": (
            candidate_review.get("selected_ck_option_class")
            == SELECTED_CK_OPTION_CLASS
            and candidate_review.get("selected_ck_constraint_family")
            == SELECTED_CK_CONSTRAINT_FAMILY
        ),
        "source_admissibility_context_exact": (
            candidate_review.get("source_rule_closeout_outcome")
            == SOURCE_RULE_CLOSEOUT_OUTCOME
            and candidate_review.get("source_candidate_constraint_id")
            == SOURCE_CANDIDATE_CONSTRAINT_ID
            and candidate_review.get("source_candidate_constraint_form")
            == SOURCE_CANDIDATE_CONSTRAINT_FORM
            and candidate_review.get("source_candidate_constraint_equation")
            == SOURCE_CANDIDATE_CONSTRAINT_EQUATION
            and candidate_review.get("source_admissibility_constraint_form")
            == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
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
            and "component pairing rule" in routes[1]["blocking_reasons"]
        ),
        "penalty_route_not_licensed": routes[2]["status"] == PENALTY_ROUTE_STATUS,
        "review_rows_all_accepted": all(
            row["status"] == "accepted" for row in review_rows
        ),
        "next_review_target_selected": (
            NEXT_TARGET
            == "review_phi_bridge_admissibility_ck_functional_embedding_packet_result"
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_PHI_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET"
    )
    route_sequence = " -> ".join(BRIDGE_ROUTE_ALIGNMENT_SEQUENCE)
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_PHI_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PHI_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_REQUIRES_REMEDIATION",
        "packet_result": PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "candidate_review_outcome": CANDIDATE_REVIEW_OUTCOME,
        "candidate_review_result": CANDIDATE_REVIEW_RESULT,
        "selected_ck_option_class": SELECTED_CK_OPTION_CLASS,
        "selected_ck_constraint_family": SELECTED_CK_CONSTRAINT_FAMILY,
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
        "embedding_routes": routes,
        "embedding_route_count": len(routes),
        "selected_embedding_route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
        "admissibility_only_route_selected": True,
        "admissibility_only_interpretation_retained": True,
        "constraint_as_admissibility_rule_selected": True,
        "route_consistency_tuple_carried_forward": True,
        "field_equation_match_component_preserved": True,
        "stress_energy_match_component_preserved": True,
        "source_residual_match_component_preserved": True,
        "source_admissibility_context_preserved": True,
        "lagrange_multiplier_route_recorded": True,
        "lagrange_multiplier_route_blocked": True,
        "lagrange_multiplier_action_form": LAGRANGE_MULTIPLIER_ACTION_FORM,
        "component_pairing_requirements": COMPONENT_PAIRING_REQUIREMENTS,
        "component_pairing_rule_selected": False,
        "multiplier_component_domain_selected": False,
        "constraint_multiplier_type_selected": False,
        "constraint_term_selected": False,
        "multiplier_type_selected": False,
        "multiplier_domain_selected": False,
        "covariance_of_multiplier_pairing_established": False,
        "boundary_terms_controlled": False,
        "variation_policy_for_embedding_selected": False,
        "penalty_route_recorded": True,
        "penalty_route_licensed": False,
        "penalty_action_form": PENALTY_ACTION_FORM,
        "functional_embedding_packet_prepared": True,
        "functional_embedding_options_recorded": True,
        "dynamical_action_embedding_selected": False,
        "dynamical_action_embedding_not_assumed": True,
        "constraint_as_action_term_selected": False,
        "bridge_candidate_recorded_as_action_term": False,
        "bridge_candidate_recorded_as_new_dynamical_law": False,
        "bridge_functional_selected": False,
        "bridge_candidate_functional_defined": False,
        "bridge_candidate_functional_selected": False,
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
        "bridge_candidate_rule_proved": False,
        "bridge_admissibility_claimed": False,
        "bridge_admissibility_proved": False,
        "bridge_route_alignment_verified": False,
        "route_consistency_tuple_proved": False,
        "field_equation_match_proved": False,
        "stress_energy_match_proved": False,
        "source_residual_match_proved": False,
        "ck_family_claimed_as_physical_law": False,
        "phi_generated_by_ck_claimed": False,
        "phi_generation_theorem_claimed": False,
        "native_generation_theorem_claimed": False,
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
            "PHI_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_OPTIONS_"
            "RECORDED_ADMISSIBILITY_ONLY"
        ),
        "mathematical_statement": (
            "The functional-embedding packet records three routes for the "
            "phi bridge-admissibility C_k candidate. The admissibility-only "
            "route C_bridge^phi = 0 is selected as a non-dynamical route-"
            "consistency rule. The Lagrange-multiplier route "
            "S_C^bridge = integral_M dVol_g Lambda_bridge dot C_bridge^phi "
            "is blocked by unselected multiplier/component pairing, domain, "
            "covariance, boundary, and variation scope. The penalty route "
            "S_C^bridge = integral_M dVol_g norm(C_bridge^phi)^2 is "
            "recorded but not licensed. No action variation is executed."
        ),
        "non_claim_boundary": (
            "This packet records bridge functional-embedding options and "
            "selects the admissibility-only route. It does not functionalize "
            "C_bridge^phi, does not embed it in S_C, does not define a C_k "
            "action term, does not select Lambda_bridge or its component "
            "pairing rule, does not select component domains, does not prove "
            "covariance of the multiplier pairing, does not control boundary "
            "terms, does not select an embedding variation policy, does not "
            "license the penalty route, does not select or define a fully "
            "concrete C_k functional, does not execute C_k variation, does "
            "not vary Lambda_bridge, does not vary the candidate with respect "
            "to phi or g, does not prove full bridge admissibility, does not "
            "prove the field-equation match, does not prove the stress-energy "
            "match, does not prove the source-residual match, does not verify "
            "the full route alignment, does not claim phi generation, does not "
            "derive V(phi), does not prove new conservation, does not prove "
            "new source admissibility, does not close QFT-GR, does not "
            "authorize semiclassical coupling, does not promote the master "
            "action, does not claim empirical validation, and does not "
            "authorize public readiness. C_k remains admissibility-only at "
            "this bridge layer and inactive as a dynamical action term."
        ),
        "critical_gate_fail_conditions": [
            "claim the multiplier route is selected as an action term",
            "claim the penalty route is licensed",
            "select Lambda_bridge multiplier type or component domains",
            "select a component pairing rule",
            "claim covariance of the multiplier pairing is established",
            "execute C_k or Lambda_bridge variation",
            "execute phi or metric variation of the candidate",
            "claim boundary terms are controlled",
            "claim full bridge admissibility is proved",
            "claim route alignment is verified",
            "claim phi is generated by C_k",
            "claim V(phi) is derived",
            "claim source admissibility or conservation newly proved",
            "claim QFT-GR closure",
            "claim semiclassical coupling",
            "promote the master action",
            "claim empirical validation or public readiness",
        ],
        "validation_policy": _validation_policy(),
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "aggregate_lean_validation_status_for_packet": AGGREGATE_TIMEOUT_STATUS,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.PhiBridgeAdmissibilityCKFunctionalEmbeddingPacket",
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
            "Build the phi bridge-admissibility C_k functional embedding packet."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    packet = build_phi_bridge_admissibility_ck_functional_embedding_packet(
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
