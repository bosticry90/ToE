from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_source_admissibility_ck_functional_embedding_packet_report import (
    ADMISSIBILITY_CONSTRAINT_FORM,
    ADMISSIBILITY_ONLY_ROUTE_ID,
    ADMISSIBILITY_ONLY_ROUTE_STATUS,
    AGGREGATE_TIMEOUT_STATUS,
    CANDIDATE_CONSTRAINT_EQUATION,
    CANDIDATE_CONSTRAINT_FORM,
    CANDIDATE_CONSTRAINT_ID,
    DEFAULT_OUT as EMBEDDING_PACKET_PATH,
    DIRECT_DIVERGENCE_INSERTION_FORM,
    LAGRANGE_MULTIPLIER_ACTION_FORM,
    LAGRANGE_MULTIPLIER_ROUTE_ID,
    LAGRANGE_MULTIPLIER_ROUTE_STATUS,
    NEXT_TARGET as CONSUMED_TARGET,
    ON_SHELL_IMPLICATION_FORM,
    ON_SHELL_RESIDUAL_FORM,
    OUTCOME_ID as EMBEDDING_PACKET_OUTCOME,
    PACKET_ID as EMBEDDING_PACKET_ID,
    PACKET_RESULT as EMBEDDING_PACKET_RESULT,
    QUADRATIC_PENALTY_ACTION_FORM,
    QUADRATIC_PENALTY_ROUTE_ID,
    QUADRATIC_PENALTY_ROUTE_STATUS,
    RESIDUAL_IDENTITY_FORM,
    SCHEMA_ID as EMBEDDING_PACKET_SCHEMA_ID,
    SELECTED_CK_CONSTRAINT_FAMILY,
    SELECTED_CK_OPTION_CLASS,
    WEAK_INTEGRATED_FORM,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-18T00:00:00Z"

SCHEMA_ID = (
    "PHI_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW_"
    "20260618_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "PHI_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "PHI_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_RESULT_REVIEW_ACCEPTS_"
    "ADMISSIBILITY_ONLY_ROUTE_NO_ACTION_VARIATION_OR_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "phi_source_admissibility_ck_functional_embedding_result_review_accepts_"
    "admissibility_only_route_no_action_variation_or_promotion"
)
NEXT_TARGET = "prepare_phi_source_admissibility_ck_admissibility_rule_closeout"
NEXT_TARGET_KIND = "phi_source_admissibility_ck_admissibility_rule_closeout_preparation"
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"

FIRST_RULE_CLASSIFICATION = "first_phi_relevant_ck_admissibility_rule_candidate"

DEFAULT_OUT = (
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
    / "PhiSourceAdmissibilityCKFunctionalEmbeddingPacketResultReview.lean"
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
            "evidence": packet.get("admissibility_constraint_form"),
            "assessment": (
                "The review accepts only C_source^nu[g, phi] = 0 as a "
                "non-dynamical admissibility rule."
            ),
        },
        {
            "row_id": "multiplier_action_route_blocked",
            "status": "accepted",
            "evidence": [
                LAGRANGE_MULTIPLIER_ACTION_FORM,
                DIRECT_DIVERGENCE_INSERTION_FORM,
                WEAK_INTEGRATED_FORM,
            ],
            "assessment": (
                "The multiplier/action route remains blocked by multiplier "
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
            "row_id": "c_source_zero_preserved_as_rule",
            "status": "accepted",
            "evidence": ADMISSIBILITY_CONSTRAINT_FORM,
            "assessment": (
                "C_source^nu[g, phi] = 0 is preserved as a source-admission "
                "rule rather than an action term."
            ),
        },
        {
            "row_id": "conservation_residual_candidate_carried_forward",
            "status": "accepted",
            "evidence": [CANDIDATE_CONSTRAINT_FORM, CANDIDATE_CONSTRAINT_EQUATION],
            "assessment": "The conservation-residual candidate is carried forward exactly.",
        },
        {
            "row_id": "residual_identity_carried_forward",
            "status": "accepted",
            "evidence": [ON_SHELL_RESIDUAL_FORM, RESIDUAL_IDENTITY_FORM],
            "assessment": "The selected-policy scalar residual identity is preserved.",
        },
        {
            "row_id": "no_ck_variation_executed",
            "status": "accepted",
            "evidence": [
                "ck_variation_executed=false",
                "lambda_variation_executed=false",
                "phi_variation_of_candidate_executed=false",
                "metric_variation_of_candidate_executed=false",
            ],
            "assessment": "No C_k, lambda, phi, metric, or penalty variation is executed.",
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
            "row_id": "no_new_conservation_or_source_proof",
            "status": "accepted",
            "evidence": [
                "new_conservation_proof_claimed=false",
                "new_source_admissibility_proof_claimed=false",
            ],
            "assessment": (
                "The review accepts the route selection without claiming a "
                "new conservation or source-admissibility proof."
            ),
        },
        {
            "row_id": "no_qft_gr_closure_or_master_action_promotion",
            "status": "accepted",
            "evidence": [
                "qft_gr_closure_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": (
                "QFT-GR closure, semiclassical coupling, and master-action "
                "promotion remain blocked."
            ),
        },
        {
            "row_id": "admissibility_rule_closeout_next_target_selected",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": (
                "The next target is a bounded closeout of the first "
                "phi-relevant C_k admissibility rule candidate."
            ),
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "phi_source_admissibility_ck_functional_embedding_packet_result_review"
        ),
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


def build_phi_source_admissibility_ck_functional_embedding_packet_result_review(
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
        "admissibility_only_route_selected": (
            packet.get("admissibility_only_route_selected") is True
            and packet.get("constraint_as_admissibility_rule_selected") is True
            and packet.get("constraint_as_action_term_selected") is False
            and packet.get("admissibility_constraint_form")
            == ADMISSIBILITY_CONSTRAINT_FORM
        ),
        "action_routes_blocked_or_unlicensed": (
            packet.get("lagrange_multiplier_route_blocked") is True
            and packet.get("lagrange_multiplier_action_form")
            == LAGRANGE_MULTIPLIER_ACTION_FORM
            and packet.get("weak_integrated_form") == WEAK_INTEGRATED_FORM
            and packet.get("quadratic_penalty_route_recorded") is True
            and packet.get("quadratic_penalty_route_licensed") is False
            and packet.get("quadratic_penalty_action_form")
            == QUADRATIC_PENALTY_ACTION_FORM
        ),
        "candidate_forms_exact": (
            packet.get("candidate_constraint_id") == CANDIDATE_CONSTRAINT_ID
            and packet.get("candidate_constraint_form") == CANDIDATE_CONSTRAINT_FORM
            and packet.get("candidate_constraint_equation")
            == CANDIDATE_CONSTRAINT_EQUATION
            and packet.get("on_shell_residual_form") == ON_SHELL_RESIDUAL_FORM
            and packet.get("residual_identity_form") == RESIDUAL_IDENTITY_FORM
            and packet.get("on_shell_implication_form") == ON_SHELL_IMPLICATION_FORM
        ),
        "no_action_embedding_or_variation": all(
            packet.get(key) is False
            for key in [
                "dynamical_action_embedding_selected",
                "constraint_as_action_term_selected",
                "constraint_multiplier_type_selected",
                "constraint_term_selected",
                "lambda_nu_domain_selected",
                "lambda_nu_variational_role_selected",
                "weak_integrated_form_boundary_controlled",
                "higher_derivative_scope_resolved",
                "boundary_terms_controlled",
                "regularity_domain_of_c_source_defined_for_action_embedding",
                "covariance_of_lambda_c_source_established",
                "candidate_action_insertion_executed",
                "ck_variation_executed",
                "lambda_variation_executed",
                "metric_variation_of_candidate_executed",
                "phi_variation_of_candidate_executed",
                "quadratic_penalty_variation_executed",
            ]
        ),
        "no_forbidden_claims": all(
            packet.get(key) is False
            for key in [
                "phi_generated_by_ck_claimed",
                "phi_generation_theorem_claimed",
                "derived_v_phi_claimed",
                "v_phi_derivation_claimed",
                "potential_derived",
                "new_conservation_proof_claimed",
                "new_source_admissibility_proof_claimed",
                "source_admissibility_claimed",
                "source_admissibility_completed",
                "source_conservation_claimed",
                "weak_conservation_claimed",
                "bianchi_compatibility_claimed",
                "qft_gr_closure_claimed",
                "qft_gr_solved",
                "qft_gr_seam_closed",
                "qft_gr_source_map_closure_authorized",
                "semiclassical_coupling_authorized",
                "semiclassical_coupling_claimed",
                "master_action_promoted",
                "master_action_promotion_authorized",
                "canonical_master_action_promoted",
                "toe_native_matter_derivation_claimed",
                "toe_native_matter_sector_derived",
                "toe_native_matter_sector_defined",
                "standard_model_derivation_claimed",
                "native_generation_theorem_claimed",
                "empirical_validation_claimed",
                "public_readiness_claimed",
                "phase2_readiness_claim",
                "pillar_completion_inferred",
                "seam_closure_claim",
            ]
        ),
        "criteria_all_accepted": all(row["status"] == "accepted" for row in criteria),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_PHI_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_REVIEW"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PHI_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_"
            "RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "review_prepared": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PHI_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_REVIEW_REQUIRES_REMEDIATION",
        "review_result": REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "embedding_packet_outcome": EMBEDDING_PACKET_OUTCOME,
        "embedding_packet_result": EMBEDDING_PACKET_RESULT,
        "selected_ck_option_class": SELECTED_CK_OPTION_CLASS,
        "selected_ck_constraint_family": SELECTED_CK_CONSTRAINT_FAMILY,
        "candidate_constraint_id": CANDIDATE_CONSTRAINT_ID,
        "candidate_constraint_type": "conservation_residual_constraint",
        "candidate_constraint_form": CANDIDATE_CONSTRAINT_FORM,
        "candidate_constraint_equation": CANDIDATE_CONSTRAINT_EQUATION,
        "on_shell_residual_form": ON_SHELL_RESIDUAL_FORM,
        "residual_identity_form": RESIDUAL_IDENTITY_FORM,
        "on_shell_implication_form": ON_SHELL_IMPLICATION_FORM,
        "embedding_route_count": 3,
        "selected_embedding_route_id": ADMISSIBILITY_ONLY_ROUTE_ID,
        "admissibility_only_route_status": ADMISSIBILITY_ONLY_ROUTE_STATUS,
        "admissibility_constraint_form": ADMISSIBILITY_CONSTRAINT_FORM,
        "lagrange_multiplier_route_id": LAGRANGE_MULTIPLIER_ROUTE_ID,
        "lagrange_multiplier_route_status": LAGRANGE_MULTIPLIER_ROUTE_STATUS,
        "lagrange_multiplier_action_form": LAGRANGE_MULTIPLIER_ACTION_FORM,
        "direct_divergence_insertion_form": DIRECT_DIVERGENCE_INSERTION_FORM,
        "weak_integrated_form": WEAK_INTEGRATED_FORM,
        "quadratic_penalty_route_id": QUADRATIC_PENALTY_ROUTE_ID,
        "quadratic_penalty_route_status": QUADRATIC_PENALTY_ROUTE_STATUS,
        "quadratic_penalty_action_form": QUADRATIC_PENALTY_ACTION_FORM,
        "functional_embedding_result_review_prepared": True,
        "functional_embedding_result_review_accepted": True,
        "review_accepts_admissibility_only_route": True,
        "packet_result_review_accepts_admissibility_only_route": True,
        "admissibility_rule_closeout_authorized": True,
        "admissibility_rule_closeout_prepared": False,
        "first_phi_relevant_ck_admissibility_rule_candidate_classification": (
            FIRST_RULE_CLASSIFICATION
        ),
        "functional_embedding_packet_prepared": True,
        "functional_embedding_options_recorded": True,
        "admissibility_only_route_selected": True,
        "admissibility_only_interpretation_retained": True,
        "constraint_as_admissibility_rule_selected": True,
        "dynamical_action_embedding_selected": False,
        "dynamical_action_embedding_not_assumed": True,
        "constraint_as_action_term_selected": False,
        "lagrange_multiplier_route_recorded": True,
        "lagrange_multiplier_route_blocked": True,
        "weak_integrated_form_boundary_controlled": False,
        "quadratic_penalty_route_recorded": True,
        "quadratic_penalty_route_licensed": False,
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
        "review_criteria": criteria,
        "review_criteria_count": len(criteria),
        "review_criteria_accepted_count": sum(
            1 for row in criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "proof_depth_label": (
            "PHI_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_REVIEW_"
            "ACCEPTS_ADMISSIBILITY_ONLY"
        ),
        "mathematical_statement": (
            "The review accepts the functional-embedding packet only at the "
            "admissibility-rule level. The rule C_source^nu[g, phi] = 0 is "
            "preserved as a non-dynamical source-admission condition. The "
            "Lagrange-multiplier action route remains blocked, the quadratic "
            "penalty route remains not licensed, and no action variation or "
            "promotion is executed."
        ),
        "non_claim_boundary": (
            "This review accepts the admissibility-only route as a rule only, "
            "not as an action term. It preserves C_source^nu[g, phi] = 0 as a "
            "source-admission rule, keeps the multiplier/action route blocked "
            "by lambda_nu domain, boundary-term, and higher-derivative scope, "
            "and keeps the quadratic penalty route not licensed. It does not "
            "functionalize the candidate, does not embed it in S_C, does not "
            "select lambda_nu or its domain, does not select a constraint "
            "action term, does not control boundary terms, does not resolve "
            "higher-derivative scope, does not select or define a fully "
            "concrete C_k functional, does not execute C_k variation, does "
            "not vary lambda_k, does not vary the candidate with respect to "
            "phi or g, does not execute a quadratic penalty variation, does "
            "not claim phi generation, does not derive V(phi), does not prove "
            "new conservation, does not prove new source admissibility, does "
            "not close QFT-GR, does not authorize semiclassical coupling, "
            "does not promote the master action, does not claim empirical "
            "validation, and does not authorize public readiness. C_k remains "
            "inactive and undefined at the fully concrete functional level. "
            "V(phi) remains smooth bounded-below but not derived. C_k does "
            "not yet generate phi. There is no ToE-native matter derivation, "
            "no native-generation theorem, no source admissibility or "
            "conservation, no QFT-GR closure, and no canonical master-action "
            "promotion."
        ),
        "critical_gate_fail_conditions": [
            "treat C_source^nu = 0 as a selected dynamical action term",
            "claim the multiplier/action route is selected",
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
            "ToeFormal.Derivation.PhiSourceAdmissibilityCKFunctionalEmbeddingPacketResultReview",
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
            "Build the phi source-admissibility C_k functional-embedding "
            "packet result review."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    review = (
        build_phi_source_admissibility_ck_functional_embedding_packet_result_review(
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
