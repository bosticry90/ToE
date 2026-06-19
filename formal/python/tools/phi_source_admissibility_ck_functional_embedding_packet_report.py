from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_source_admissibility_ck_constraint_candidate_packet_result_review_report import (
    AGGREGATE_TIMEOUT_STATUS,
    CANDIDATE_ACTION_INSERTION_FORM,
    CANDIDATE_CONSTRAINT_EQUATION,
    CANDIDATE_CONSTRAINT_FORM,
    CANDIDATE_CONSTRAINT_ID,
    DEFAULT_OUT as CANDIDATE_REVIEW_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    ON_SHELL_IMPLICATION_FORM,
    ON_SHELL_RESIDUAL_FORM,
    OUTCOME_ID as CANDIDATE_REVIEW_OUTCOME,
    PACKET_ID as CANDIDATE_REVIEW_PACKET_ID,
    RESIDUAL_IDENTITY_FORM,
    REVIEW_RESULT as CANDIDATE_REVIEW_RESULT,
    ROUTE_BUNDLE_ADMISSIBILITY_FORM,
    SCHEMA_ID as CANDIDATE_REVIEW_SCHEMA_ID,
    SELECTED_CK_CONSTRAINT_FAMILY,
    SELECTED_CK_OPTION_CLASS,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-18T00:00:00Z"

SCHEMA_ID = "PHI_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_20260618_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "PHI_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_v0"
PACKET_RESULT = (
    "PHI_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_OPTIONS_RECORDED_"
    "ADMISSIBILITY_ONLY_ROUTE_SELECTED_NO_ACTION_VARIATION"
)
OUTCOME_ID = (
    "PHI_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_PREPARED_"
    + PACKET_RESULT
)
PACKET_CLASSIFICATION = (
    "phi_source_admissibility_ck_functional_embedding_packet_records_options_"
    "and_selects_admissibility_only_no_action_variation"
)
NEXT_TARGET = "review_phi_source_admissibility_ck_functional_embedding_packet_result"
NEXT_TARGET_KIND = "phi_source_admissibility_ck_functional_embedding_packet_result_review"
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"

ADMISSIBILITY_ONLY_ROUTE_ID = "phi_source_ck_admissibility_only_route"
ADMISSIBILITY_CONSTRAINT_FORM = "C_source^nu[g, phi] = 0"
ADMISSIBILITY_ONLY_ROUTE_STATUS = "selected_non_dynamical_admissibility_rule"
LAGRANGE_MULTIPLIER_ROUTE_ID = "phi_source_ck_lagrange_multiplier_action_route"
LAGRANGE_MULTIPLIER_ACTION_FORM = (
    "S_C^phi = integral_M dVol_g lambda_nu C_source^nu"
)
DIRECT_DIVERGENCE_INSERTION_FORM = (
    "S_C^phi = integral_M dVol_g lambda_nu nabla_mu T_phi^{mu nu}"
)
WEAK_INTEGRATED_FORM = (
    "integral_M dVol_g lambda_nu nabla_mu T_phi^{mu nu} = - integral_M "
    "dVol_g (nabla_mu lambda_nu) T_phi^{mu nu} + boundary"
)
LAGRANGE_MULTIPLIER_ROUTE_STATUS = (
    "blocked_by_multiplier_domain_boundary_and_higher_derivative_scope"
)
QUADRATIC_PENALTY_ROUTE_ID = "phi_source_ck_quadratic_penalty_route"
QUADRATIC_PENALTY_ACTION_FORM = (
    "S_C^phi = integral_M dVol_g C_source_nu C_source^nu"
)
QUADRATIC_PENALTY_ROUTE_STATUS = "recorded_not_licensed"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_20260618_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiSourceAdmissibilityCKFunctionalEmbeddingPacket.lean"
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
            "route_type": "admissibility_only_rule",
            "status": ADMISSIBILITY_ONLY_ROUTE_STATUS,
            "constraint_form": ADMISSIBILITY_CONSTRAINT_FORM,
            "plain_meaning": (
                "Only scalar configurations whose stress-energy conservation "
                "residual vanishes are admitted as gravity sources."
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
            "direct_divergence_insertion_form": DIRECT_DIVERGENCE_INSERTION_FORM,
            "weak_integrated_form": WEAK_INTEGRATED_FORM,
            "blocking_reasons": [
                "lambda_nu multiplier type/domain not selected",
                "boundary terms not controlled",
                "higher-derivative scope not controlled",
                "variation with respect to phi and g not licensed",
            ],
            "action_term_selected": False,
            "action_variation_executed": False,
            "selected_for_current_packet": False,
        },
        {
            "route_id": QUADRATIC_PENALTY_ROUTE_ID,
            "route_type": "quadratic_penalty_action_embedding",
            "status": QUADRATIC_PENALTY_ROUTE_STATUS,
            "action_form": QUADRATIC_PENALTY_ACTION_FORM,
            "blocking_reasons": [
                "would modify dynamics",
                "requires metric and regularity control",
                "requires derivative-order control",
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
            "assessment": "The candidate review authorized this functional-embedding packet.",
        },
        {
            "row_id": "conservation_residual_candidate_carried_forward",
            "status": "accepted",
            "evidence": [CANDIDATE_CONSTRAINT_FORM, CANDIDATE_CONSTRAINT_EQUATION],
            "assessment": "The conservation residual candidate is carried forward exactly.",
        },
        {
            "row_id": "route_identity_carried_forward",
            "status": "accepted",
            "evidence": [ON_SHELL_RESIDUAL_FORM, RESIDUAL_IDENTITY_FORM],
            "assessment": "The selected-policy residual identity is preserved.",
        },
        {
            "row_id": "three_embedding_routes_recorded",
            "status": "accepted",
            "evidence": [
                ADMISSIBILITY_ONLY_ROUTE_ID,
                LAGRANGE_MULTIPLIER_ROUTE_ID,
                QUADRATIC_PENALTY_ROUTE_ID,
            ],
            "assessment": "Admissibility-only, multiplier-action, and quadratic-penalty routes are recorded.",
        },
        {
            "row_id": "admissibility_only_route_selected",
            "status": "accepted",
            "evidence": ADMISSIBILITY_CONSTRAINT_FORM,
            "assessment": "The packet selects only the non-dynamical admissibility rule.",
        },
        {
            "row_id": "lagrange_multiplier_route_blocked",
            "status": "accepted",
            "evidence": [LAGRANGE_MULTIPLIER_ACTION_FORM, WEAK_INTEGRATED_FORM],
            "assessment": (
                "The multiplier route is recorded but blocked by multiplier "
                "domain, boundary-term, and higher-derivative scope."
            ),
        },
        {
            "row_id": "quadratic_penalty_route_not_licensed",
            "status": "accepted",
            "evidence": QUADRATIC_PENALTY_ACTION_FORM,
            "assessment": "The quadratic penalty route is recorded but not licensed.",
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
            "row_id": "no_new_proof_or_generation_claim",
            "status": "accepted",
            "evidence": [
                "phi_generated_by_ck_claimed=false",
                "potential_derived=false",
                "new_conservation_proof_claimed=false",
                "new_source_admissibility_proof_claimed=false",
            ],
            "assessment": "The packet makes no generation, potential, conservation, or source-admissibility proof claim.",
        },
        {
            "row_id": "no_closure_or_promotion_claim",
            "status": "accepted",
            "evidence": [
                "qft_gr_closure_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": "QFT-GR closure and master-action promotion remain blocked.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "phi_source_admissibility_ck_functional_embedding_packet",
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


def build_phi_source_admissibility_ck_functional_embedding_packet(
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
        "candidate_forms_carried_forward": (
            candidate_review.get("candidate_constraint_id") == CANDIDATE_CONSTRAINT_ID
            and candidate_review.get("candidate_constraint_form")
            == CANDIDATE_CONSTRAINT_FORM
            and candidate_review.get("candidate_constraint_equation")
            == CANDIDATE_CONSTRAINT_EQUATION
            and candidate_review.get("on_shell_residual_form") == ON_SHELL_RESIDUAL_FORM
            and candidate_review.get("residual_identity_form") == RESIDUAL_IDENTITY_FORM
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
            and "higher-derivative scope not controlled" in routes[1]["blocking_reasons"]
        ),
        "quadratic_route_not_licensed": (
            routes[2]["status"] == QUADRATIC_PENALTY_ROUTE_STATUS
        ),
        "review_rows_all_accepted": all(
            row["status"] == "accepted" for row in review_rows
        ),
        "next_review_target_selected": (
            NEXT_TARGET
            == "review_phi_source_admissibility_ck_functional_embedding_packet_result"
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_PHI_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_PHI_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PHI_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_REQUIRES_REMEDIATION",
        "packet_result": PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "candidate_review_outcome": CANDIDATE_REVIEW_OUTCOME,
        "selected_ck_option_class": SELECTED_CK_OPTION_CLASS,
        "selected_ck_constraint_family": SELECTED_CK_CONSTRAINT_FAMILY,
        "candidate_constraint_id": CANDIDATE_CONSTRAINT_ID,
        "candidate_constraint_type": "conservation_residual_constraint",
        "candidate_constraint_form": CANDIDATE_CONSTRAINT_FORM,
        "candidate_constraint_equation": CANDIDATE_CONSTRAINT_EQUATION,
        "on_shell_residual_form": ON_SHELL_RESIDUAL_FORM,
        "residual_identity_form": RESIDUAL_IDENTITY_FORM,
        "on_shell_implication_form": ON_SHELL_IMPLICATION_FORM,
        "candidate_action_insertion_form": CANDIDATE_ACTION_INSERTION_FORM,
        "route_bundle_admissibility_form": ROUTE_BUNDLE_ADMISSIBILITY_FORM,
        "embedding_routes": routes,
        "embedding_route_count": len(routes),
        "selected_embedding_route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
        "admissibility_only_route_selected": True,
        "admissibility_constraint_form": ADMISSIBILITY_CONSTRAINT_FORM,
        "lagrange_multiplier_route_recorded": True,
        "lagrange_multiplier_route_blocked": True,
        "lagrange_multiplier_action_form": LAGRANGE_MULTIPLIER_ACTION_FORM,
        "direct_divergence_insertion_form": DIRECT_DIVERGENCE_INSERTION_FORM,
        "weak_integrated_form": WEAK_INTEGRATED_FORM,
        "weak_integrated_form_boundary_controlled": False,
        "quadratic_penalty_route_recorded": True,
        "quadratic_penalty_route_licensed": False,
        "quadratic_penalty_action_form": QUADRATIC_PENALTY_ACTION_FORM,
        "functional_embedding_packet_prepared": True,
        "functional_embedding_options_recorded": True,
        "admissibility_only_interpretation_retained": True,
        "dynamical_action_embedding_selected": False,
        "dynamical_action_embedding_not_assumed": True,
        "constraint_as_admissibility_rule_selected": True,
        "constraint_as_action_term_selected": False,
        "constraint_multiplier_type_selected": False,
        "constraint_term_selected": False,
        "lambda_nu_domain_selected": False,
        "lambda_nu_variational_role_selected": False,
        "higher_derivative_scope_resolved": False,
        "boundary_terms_controlled": False,
        "regularity_domain_of_c_source_defined_for_action_embedding": False,
        "covariance_of_lambda_c_source_established": False,
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
        "quadratic_penalty_variation_executed": False,
        "ck_family_claimed_as_physical_law": False,
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
        "review_rows": review_rows,
        "review_row_count": len(review_rows),
        "review_row_accepted_count": sum(
            1 for row in review_rows if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "proof_depth_label": (
            "PHI_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_OPTIONS_"
            "RECORDED_ADMISSIBILITY_ONLY"
        ),
        "mathematical_statement": (
            "The functional-embedding packet records three routes for the "
            "phi source-admissibility C_k candidate. The admissibility-only "
            "route C_source^nu[g, phi] = 0 is selected as a non-dynamical "
            "source-admission rule. The Lagrange-multiplier route "
            "S_C^phi = integral_M dVol_g lambda_nu C_source^nu is blocked by "
            "unselected multiplier domain, boundary terms, and higher-"
            "derivative scope. The quadratic penalty route is recorded but "
            "not licensed. No action variation is executed."
        ),
        "non_claim_boundary": (
            "This packet records functional-embedding options and selects the "
            "admissibility-only route. It does not functionalize the "
            "conservation residual, does not embed it in S_C, does not select "
            "lambda_nu or its domain, does not select a constraint action "
            "term, does not control boundary terms, does not resolve "
            "higher-derivative scope, does not select or define a fully "
            "concrete C_k functional, does not execute C_k variation, does "
            "not vary lambda_k, does not vary the candidate with respect to "
            "phi or g, does not execute a quadratic penalty variation, does "
            "not claim phi generation, does not derive V(phi), does not prove "
            "new conservation, does not prove new source admissibility, does "
            "not close QFT-GR, does not authorize semiclassical coupling, "
            "does not promote the master action, does not claim empirical "
            "validation, and does not authorize public readiness. C_k remains "
            "inactive and undefined at the fully concrete functional level, "
            "and C_k content is not fully defined. V(phi) remains smooth "
            "bounded-below but not derived. C_k does not yet generate phi. "
            "There is no ToE-native matter derivation, no native-generation "
            "theorem, no source admissibility or conservation, no QFT-GR "
            "closure, and no canonical master-action promotion."
        ),
        "critical_gate_fail_conditions": [
            "claim the multiplier route is selected as an action term",
            "claim the quadratic penalty route is licensed",
            "select lambda_nu multiplier type or domain",
            "execute C_k or lambda variation",
            "execute phi or metric variation of the candidate",
            "claim boundary terms are controlled",
            "claim higher-derivative scope is resolved",
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
            "ToeFormal.Derivation.PhiSourceAdmissibilityCKFunctionalEmbeddingPacket",
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
        description="Build the phi source-admissibility C_k functional embedding packet."
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    packet = build_phi_source_admissibility_ck_functional_embedding_packet(
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
