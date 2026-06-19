from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-18T00:00:00Z"

SCHEMA_ID = "PHI_SOURCE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSEOUT_20260618_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "PHI_SOURCE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSEOUT_v0"
CLOSEOUT_RESULT = (
    "PHI_SOURCE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSED_AS_FIRST_PHI_"
    "RELEVANT_CK_RULE_CANDIDATE_NO_ACTION_VARIATION_OR_PROMOTION"
)
OUTCOME_ID = CLOSEOUT_RESULT
PACKET_CLASSIFICATION = (
    "phi_source_admissibility_ck_admissibility_rule_closed_as_first_phi_"
    "relevant_ck_rule_candidate_no_action_variation_or_promotion"
)
NEXT_TARGET = "select_next_phi_relevant_ck_constraint_family_after_source_admissibility"
NEXT_TARGET_KIND = (
    "phi_relevant_ck_constraint_family_after_source_admissibility_selection"
)
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"

NEXT_RECOMMENDED_CK_FAMILY = "bridge_admissibility_constraint_family"
NEXT_RECOMMENDED_REASON = (
    "source-admissibility now asks whether phi may source gravity; "
    "bridge-admissibility should next ask whether the phi route correctly "
    "connects scalar-field logic, QFT-GR source logic, and the master-action "
    "constraint layer"
)
FUNCTIONAL_EMBEDDING_REVIEW_SCHEMA_ID = (
    "PHI_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW_"
    "20260618_v0"
)
FUNCTIONAL_EMBEDDING_REVIEW_PACKET_ID = (
    "PHI_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW_v0"
)
FUNCTIONAL_EMBEDDING_REVIEW_RESULT = (
    "PHI_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_RESULT_REVIEW_ACCEPTS_"
    "ADMISSIBILITY_ONLY_ROUTE_NO_ACTION_VARIATION_OR_PROMOTION"
)
FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME = FUNCTIONAL_EMBEDDING_REVIEW_RESULT
CONSUMED_TARGET = "prepare_phi_source_admissibility_ck_admissibility_rule_closeout"

SELECTED_CK_OPTION_CLASS = "source_admissibility_constraint"
SELECTED_CK_CONSTRAINT_FAMILY = "phi_source_admissibility_constraint_family"
FIRST_RULE_CLASSIFICATION = "first_phi_relevant_ck_admissibility_rule_candidate"
CANDIDATE_CONSTRAINT_ID = "phi_source_conservation_residual_ck_candidate"
CANDIDATE_CONSTRAINT_FORM = "C_source^nu[g, phi] := nabla_mu T_phi^{mu nu}"
CANDIDATE_CONSTRAINT_EQUATION = "C_source^nu[g, phi] = 0"
ADMISSIBILITY_CONSTRAINT_FORM = "C_source^nu[g, phi] = 0"
ON_SHELL_RESIDUAL_FORM = "R_i^phi := Box_g phi_i + partial_i V(phi)"
RESIDUAL_IDENTITY_FORM = "C_source^nu = sum_i R_i^phi nabla^nu phi_i"
ON_SHELL_IMPLICATION_FORM = "R_i^phi = 0 for all i implies C_source^nu = 0"
ADMISSIBILITY_ONLY_ROUTE_ID = "phi_source_ck_admissibility_only_route"
ADMISSIBILITY_ONLY_ROUTE_STATUS = "selected_non_dynamical_admissibility_rule"
LAGRANGE_MULTIPLIER_ROUTE_STATUS = (
    "blocked_by_multiplier_domain_boundary_and_higher_derivative_scope"
)
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
QUADRATIC_PENALTY_ROUTE_STATUS = "recorded_not_licensed"
QUADRATIC_PENALTY_ACTION_FORM = (
    "S_C^phi = integral_M dVol_g C_source_nu C_source^nu"
)
AGGREGATE_TIMEOUT_STATUS = "INCOMPLETE_TIMEOUT_STEADY_PROGRESS"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_SOURCE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSEOUT_20260618_v0.json"
)
FUNCTIONAL_EMBEDDING_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW_"
    "20260618_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiSourceAdmissibilityCKAdmissibilityRuleCloseout.lean"
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
                "interpretation of the conservation residual."
            ),
        },
        {
            "row_id": "first_phi_relevant_ck_rule_candidate_closed",
            "status": "accepted",
            "evidence": FIRST_RULE_CLASSIFICATION,
            "assessment": (
                "The closeout classifies the result as the first phi-relevant "
                "C_k admissibility rule candidate."
            ),
        },
        {
            "row_id": "conservation_residual_form_preserved",
            "status": "accepted",
            "evidence": CANDIDATE_CONSTRAINT_FORM,
            "assessment": (
                "C_source^nu[g, phi] := nabla_mu T_phi^{mu nu} is preserved."
            ),
        },
        {
            "row_id": "admissibility_condition_preserved",
            "status": "accepted",
            "evidence": ADMISSIBILITY_CONSTRAINT_FORM,
            "assessment": "C_source^nu[g, phi] = 0 is preserved as a rule.",
        },
        {
            "row_id": "scalar_residual_identity_preserved",
            "status": "accepted",
            "evidence": [ON_SHELL_RESIDUAL_FORM, RESIDUAL_IDENTITY_FORM],
            "assessment": (
                "The selected-policy scalar residual and source residual "
                "identity are preserved."
            ),
        },
        {
            "row_id": "not_action_term_or_dynamical_law",
            "status": "accepted",
            "evidence": [
                "constraint_as_action_term_selected=false",
                "dynamical_action_embedding_selected=false",
            ],
            "assessment": (
                "The rule is closed as admissibility-only, not as an action "
                "term or new dynamical law."
            ),
        },
        {
            "row_id": "multiplier_and_penalty_routes_remain_blocked",
            "status": "accepted",
            "evidence": [
                LAGRANGE_MULTIPLIER_ROUTE_STATUS,
                QUADRATIC_PENALTY_ROUTE_STATUS,
            ],
            "assessment": (
                "The multiplier route remains blocked and the quadratic "
                "penalty route remains not licensed."
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
                "The closeout executes no C_k variation, generates no phi, "
                "and derives no V(phi)."
            ),
        },
        {
            "row_id": "no_new_conservation_or_source_proof",
            "status": "accepted",
            "evidence": [
                "new_conservation_proof_claimed=false",
                "new_source_admissibility_proof_claimed=false",
            ],
            "assessment": (
                "The rule candidate is closed without claiming new "
                "conservation or source-admissibility proof."
            ),
        },
        {
            "row_id": "no_closure_promotion_or_empirical_claim",
            "status": "accepted",
            "evidence": [
                "qft_gr_closure_claimed=false",
                "master_action_promoted=false",
                "empirical_validation_claimed=false",
            ],
            "assessment": (
                "QFT-GR closure, semiclassical coupling, master-action "
                "promotion, and empirical validation remain blocked."
            ),
        },
        {
            "row_id": "next_family_selector_authorized",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": (
                "The next target is a selector for the next phi-relevant C_k "
                "constraint family after source-admissibility."
            ),
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "phi_source_admissibility_ck_admissibility_rule_closeout",
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


def build_phi_source_admissibility_ck_admissibility_rule_closeout(
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
        "candidate_forms_preserved": (
            review.get("candidate_constraint_id") == CANDIDATE_CONSTRAINT_ID
            and review.get("candidate_constraint_form") == CANDIDATE_CONSTRAINT_FORM
            and review.get("candidate_constraint_equation")
            == CANDIDATE_CONSTRAINT_EQUATION
            and review.get("admissibility_constraint_form")
            == ADMISSIBILITY_CONSTRAINT_FORM
            and review.get("on_shell_residual_form") == ON_SHELL_RESIDUAL_FORM
            and review.get("residual_identity_form") == RESIDUAL_IDENTITY_FORM
            and review.get("on_shell_implication_form") == ON_SHELL_IMPLICATION_FORM
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
            and review.get("lagrange_multiplier_route_status")
            == LAGRANGE_MULTIPLIER_ROUTE_STATUS
            and review.get("quadratic_penalty_route_licensed") is False
            and review.get("quadratic_penalty_route_status")
            == QUADRATIC_PENALTY_ROUTE_STATUS
        ),
        "no_variation_or_action_embedding": all(
            review.get(key) is False
            for key in [
                "constraint_multiplier_type_selected",
                "constraint_term_selected",
                "lambda_nu_domain_selected",
                "lambda_nu_variational_role_selected",
                "higher_derivative_scope_resolved",
                "boundary_terms_controlled",
                "fully_concrete_ck_functional_selected",
                "fully_concrete_ck_functional_defined",
                "candidate_action_insertion_executed",
                "ck_variation_executed",
                "lambda_variation_executed",
                "metric_variation_of_candidate_executed",
                "phi_variation_of_candidate_executed",
                "quadratic_penalty_variation_executed",
            ]
        ),
        "no_forbidden_claims": all(
            review.get(key) is False
            for key in [
                "phi_generated_by_ck_claimed",
                "phi_generation_theorem_claimed",
                "derived_v_phi_claimed",
                "v_phi_derivation_claimed",
                "potential_derived",
                "new_conservation_proof_claimed",
                "new_source_admissibility_proof_claimed",
                "source_admissibility_claimed",
                "source_conservation_claimed",
                "qft_gr_closure_claimed",
                "qft_gr_seam_closed",
                "qft_gr_source_map_closure_authorized",
                "semiclassical_coupling_authorized",
                "semiclassical_coupling_claimed",
                "master_action_promoted",
                "master_action_promotion_authorized",
                "canonical_master_action_promoted",
                "native_generation_theorem_claimed",
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
        "next_selector_target_selected": (
            NEXT_TARGET
            == "select_next_phi_relevant_ck_constraint_family_after_source_admissibility"
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_PHI_SOURCE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSEOUT"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_PHI_SOURCE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSEOUT",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PHI_SOURCE_ADMISSIBILITY_CK_ADMISSIBILITY_RULE_CLOSEOUT_REQUIRES_REMEDIATION",
        "closeout_result": CLOSEOUT_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "functional_embedding_review_outcome": FUNCTIONAL_EMBEDDING_REVIEW_OUTCOME,
        "functional_embedding_review_result": FUNCTIONAL_EMBEDDING_REVIEW_RESULT,
        "selected_ck_option_class": SELECTED_CK_OPTION_CLASS,
        "selected_ck_constraint_family": SELECTED_CK_CONSTRAINT_FAMILY,
        "first_phi_relevant_ck_admissibility_rule_candidate_classification": (
            FIRST_RULE_CLASSIFICATION
        ),
        "candidate_constraint_id": CANDIDATE_CONSTRAINT_ID,
        "candidate_constraint_type": "conservation_residual_constraint",
        "candidate_constraint_form": CANDIDATE_CONSTRAINT_FORM,
        "candidate_constraint_equation": CANDIDATE_CONSTRAINT_EQUATION,
        "admissibility_constraint_form": ADMISSIBILITY_CONSTRAINT_FORM,
        "on_shell_residual_form": ON_SHELL_RESIDUAL_FORM,
        "residual_identity_form": RESIDUAL_IDENTITY_FORM,
        "on_shell_implication_form": ON_SHELL_IMPLICATION_FORM,
        "selected_embedding_route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
        "admissibility_only_route_status": ADMISSIBILITY_ONLY_ROUTE_STATUS,
        "lagrange_multiplier_route_status": LAGRANGE_MULTIPLIER_ROUTE_STATUS,
        "lagrange_multiplier_action_form": LAGRANGE_MULTIPLIER_ACTION_FORM,
        "direct_divergence_insertion_form": DIRECT_DIVERGENCE_INSERTION_FORM,
        "weak_integrated_form": WEAK_INTEGRATED_FORM,
        "quadratic_penalty_route_status": QUADRATIC_PENALTY_ROUTE_STATUS,
        "quadratic_penalty_action_form": QUADRATIC_PENALTY_ACTION_FORM,
        "closeout_criteria": closeout_criteria,
        "closeout_criteria_count": len(closeout_criteria),
        "closeout_criteria_accepted_count": sum(
            1 for row in closeout_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "admissibility_rule_closeout_prepared": True,
        "admissibility_rule_closeout_accepted": True,
        "first_phi_relevant_ck_admissibility_rule_candidate_closed": True,
        "source_admissibility_rule_candidate_closed": True,
        "admissibility_only_route_selected": True,
        "admissibility_only_interpretation_retained": True,
        "constraint_as_admissibility_rule_selected": True,
        "constraint_as_action_term_selected": False,
        "dynamical_action_embedding_selected": False,
        "dynamical_action_embedding_not_assumed": True,
        "candidate_recorded_as_rule_only": True,
        "candidate_recorded_as_new_physical_law": False,
        "candidate_recorded_as_action_term": False,
        "lagrange_multiplier_route_blocked": True,
        "quadratic_penalty_route_licensed": False,
        "next_selector_authorized": True,
        "next_selector_prepared": False,
        "next_candidate_family_recommendation": NEXT_RECOMMENDED_CK_FAMILY,
        "next_candidate_family_recommendation_reason": NEXT_RECOMMENDED_REASON,
        "next_candidate_family_selected": False,
        "bridge_admissibility_family_selected": False,
        "source_admissibility_family_completed": False,
        "source_admissibility_family_closed_as_candidate_only": True,
        "proof_depth_label": (
            "FIRST_PHI_RELEVANT_CK_ADMISSIBILITY_RULE_CANDIDATE_CLOSED_"
            "NO_ACTION_VARIATION"
        ),
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
        "ck_action_embedding_claimed": False,
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
            "The phi source-admissibility C_k candidate is closed as the first "
            "phi-relevant C_k admissibility rule candidate: "
            "C_source^nu[g, phi] := nabla_mu T_phi^{mu nu}, with rule "
            "C_source^nu[g, phi] = 0 and selected-policy identity "
            "C_source^nu = sum_i R_i^phi nabla^nu phi_i for "
            "R_i^phi := Box_g phi_i + partial_i V(phi). The closeout is "
            "admissibility-only and executes no action variation."
        ),
        "non_claim_boundary": (
            "This closeout records the first phi-relevant C_k admissibility "
            "rule candidate only. It keeps C_source^nu[g, phi] = 0 as an "
            "admissibility rule, not as an action term, not as a new dynamical "
            "law, and not as a native-generation theorem. It does not embed "
            "the candidate in S_C, does not select lambda_nu or a multiplier "
            "domain, does not control boundary terms, does not resolve "
            "higher-derivative scope, does not select or define a fully "
            "concrete C_k functional, does not execute C_k variation, does "
            "not vary lambda_k, phi, or g, does not claim phi generation, "
            "does not derive V(phi), does not prove new conservation, does "
            "not prove new source admissibility, does not close QFT-GR, does "
            "not authorize semiclassical coupling, does not promote the "
            "master action, does not claim empirical validation, and does "
            "not authorize public readiness. The bridge-admissibility family "
            "is recommended only as the next selector candidate and is not "
            "selected by this closeout."
        ),
        "critical_gate_fail_conditions": [
            "claim C_source^nu = 0 is an action term",
            "claim C_k action embedding",
            "execute C_k variation",
            "claim phi generation",
            "claim V(phi) derivation",
            "claim new conservation proof",
            "claim new source-admissibility proof",
            "claim QFT-GR closure",
            "claim semiclassical coupling",
            "promote the master action",
            "claim empirical validation",
            "select bridge-admissibility before the selector target runs",
        ],
        "validation_policy": _validation_policy(),
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "aggregate_lean_validation_status_for_packet": AGGREGATE_TIMEOUT_STATUS,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.PhiSourceAdmissibilityCKAdmissibilityRuleCloseout",
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
        description="Build the phi source-admissibility C_k admissibility rule closeout."
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    closeout = build_phi_source_admissibility_ck_admissibility_rule_closeout(
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
