from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_source_admissibility_ck_constraint_candidate_packet_report import (
    AGGREGATE_TIMEOUT_STATUS,
    CANDIDATE_ACTION_INSERTION_FORM,
    CANDIDATE_CONSTRAINT_EQUATION,
    CANDIDATE_CONSTRAINT_FORM,
    CANDIDATE_CONSTRAINT_ID,
    DEFAULT_OUT as CANDIDATE_PACKET_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    ON_SHELL_IMPLICATION_FORM,
    ON_SHELL_RESIDUAL_FORM,
    OUTCOME_ID as CANDIDATE_PACKET_OUTCOME,
    PACKET_ID as CANDIDATE_PACKET_ID,
    PACKET_RESULT as CANDIDATE_PACKET_RESULT,
    RESIDUAL_IDENTITY_FORM,
    ROUTE_BUNDLE_ADMISSIBILITY_FORM,
    SCHEMA_ID as CANDIDATE_PACKET_SCHEMA_ID,
    SELECTED_CK_CONSTRAINT_FAMILY,
    SELECTED_CK_OPTION_CLASS,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-18T00:00:00Z"

SCHEMA_ID = (
    "PHI_SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_RESULT_REVIEW_"
    "20260618_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "PHI_SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "PHI_SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_RESULT_REVIEW_ACCEPTS_"
    "CONSERVATION_RESIDUAL_CANDIDATE_NO_FUNCTIONALIZATION_OR_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "phi_source_admissibility_ck_constraint_candidate_result_review_accepts_"
    "conservation_residual_candidate_no_functionalization_or_promotion"
)
NEXT_TARGET = "prepare_phi_source_admissibility_ck_functional_embedding_packet"
NEXT_TARGET_KIND = "phi_source_admissibility_ck_functional_embedding_packet_preparation"
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_RESULT_REVIEW_"
    "20260618_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiSourceAdmissibilityCKConstraintCandidatePacketResultReview.lean"
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
            "row_id": "candidate_recorded_as_candidate_only",
            "status": "accepted",
            "evidence": packet.get("candidate_constraint_is_condition_not_physical_law"),
            "assessment": (
                "C_source^nu is recorded as a candidate admissibility condition "
                "only, not as a new physical law."
            ),
        },
        {
            "row_id": "conservation_residual_form_carried_forward_exactly",
            "status": "accepted",
            "evidence": CANDIDATE_CONSTRAINT_FORM,
            "assessment": (
                "The candidate form is carried forward exactly as "
                "C_source^nu[g, phi] := nabla_mu T_phi^{mu nu}."
            ),
        },
        {
            "row_id": "candidate_equation_carried_forward_exactly",
            "status": "accepted",
            "evidence": CANDIDATE_CONSTRAINT_EQUATION,
            "assessment": (
                "The candidate admissibility equation is carried forward as "
                "C_source^nu[g, phi] = 0."
            ),
        },
        {
            "row_id": "scalar_residual_under_selected_policy_carried_forward",
            "status": "accepted",
            "evidence": ON_SHELL_RESIDUAL_FORM,
            "assessment": (
                "The selected-policy scalar residual is carried forward as "
                "R_i^phi := Box_g phi_i + partial_i V(phi)."
            ),
        },
        {
            "row_id": "route_identity_carried_forward",
            "status": "accepted",
            "evidence": RESIDUAL_IDENTITY_FORM,
            "assessment": (
                "The route identity C_source^nu = sum_i R_i^phi nabla^nu phi_i "
                "is accepted as the recorded candidate route identity."
            ),
        },
        {
            "row_id": "candidate_action_insertion_not_functionalized",
            "status": "accepted",
            "evidence": CANDIDATE_ACTION_INSERTION_FORM,
            "assessment": (
                "The possible multiplier insertion is noted only as future "
                "scope; the review does not functionalize or embed it."
            ),
        },
        {
            "row_id": "no_full_ck_functional_selected",
            "status": "accepted",
            "evidence": "fully_concrete_ck_functional_defined=false",
            "assessment": "No full C_k functional is selected or defined.",
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
            "assessment": "No C_k, lambda, phi, or metric variation is executed.",
        },
        {
            "row_id": "no_phi_generation_or_potential_derivation_claimed",
            "status": "accepted",
            "evidence": [
                "phi_generation_theorem_claimed=false",
                "phi_generated_by_ck_claimed=false",
                "potential_derived=false",
            ],
            "assessment": "The review claims neither phi generation nor V(phi) derivation.",
        },
        {
            "row_id": "no_new_conservation_or_source_admissibility_proof",
            "status": "accepted",
            "evidence": [
                "new_conservation_proof_claimed=false",
                "new_source_admissibility_proof_claimed=false",
            ],
            "assessment": (
                "The candidate shape is accepted without claiming a new "
                "conservation or source-admissibility proof."
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
                "The review preserves no QFT-GR closure and no master-action "
                "promotion."
            ),
        },
        {
            "row_id": "functional_embedding_next_target_selected",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": (
                "The next target is a functional-embedding packet that can ask "
                "whether the residual candidate is admissibility-only or a "
                "legitimate action constraint term."
            ),
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "phi_source_admissibility_ck_constraint_candidate_packet_result_review"
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


def build_phi_source_admissibility_ck_constraint_candidate_packet_result_review(
    *,
    candidate_packet_path: Path = CANDIDATE_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(candidate_packet_path)
    criteria = _review_criteria(packet)
    acceptance_criteria = {
        "consumes_expected_review_target": (
            packet.get("schema_id") == CANDIDATE_PACKET_SCHEMA_ID
            and packet.get("packet_id") == CANDIDATE_PACKET_ID
            and packet.get("outcome_id") == CANDIDATE_PACKET_OUTCOME
            and packet.get("packet_result") == CANDIDATE_PACKET_RESULT
            and packet.get("selected_next_target") == CONSUMED_TARGET
            and packet.get("accepted") is True
        ),
        "candidate_only_boundary_carried_forward": (
            packet.get("candidate_constraint_is_condition_not_physical_law") is True
            and packet.get("candidate_constraint_shape_recorded") is True
        ),
        "conservation_residual_shape_exact": (
            packet.get("candidate_constraint_id") == CANDIDATE_CONSTRAINT_ID
            and packet.get("candidate_constraint_form") == CANDIDATE_CONSTRAINT_FORM
            and packet.get("candidate_constraint_equation")
            == CANDIDATE_CONSTRAINT_EQUATION
        ),
        "residual_identity_exact": (
            packet.get("on_shell_residual_form") == ON_SHELL_RESIDUAL_FORM
            and packet.get("residual_identity_form") == RESIDUAL_IDENTITY_FORM
            and packet.get("on_shell_implication_form") == ON_SHELL_IMPLICATION_FORM
        ),
        "selected_family_exact": (
            packet.get("selected_ck_option_class") == SELECTED_CK_OPTION_CLASS
            and packet.get("selected_ck_constraint_family")
            == SELECTED_CK_CONSTRAINT_FAMILY
        ),
        "no_functionalization_or_variation": all(
            packet.get(key) is False
            for key in [
                "fully_concrete_ck_functional_defined",
                "concrete_ck_functional_selected",
                "concrete_ck_functional_defined",
                "ck_functional_formula_fully_defined",
                "ck_functional_formula_selected",
                "candidate_action_insertion_executed",
                "ck_variation_executed",
                "lambda_variation_executed",
                "metric_variation_of_candidate_executed",
                "phi_variation_of_candidate_executed",
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
                "source_conservation_claimed",
                "qft_gr_closure_claimed",
                "master_action_promoted",
                "canonical_master_action_promoted",
                "native_generation_theorem_claimed",
            ]
        ),
        "criteria_all_accepted": all(row["status"] == "accepted" for row in criteria),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_PHI_SOURCE_ADMISSIBILITY_CK_CANDIDATE_REVIEW"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PHI_SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_"
            "RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PHI_SOURCE_ADMISSIBILITY_CK_CANDIDATE_REVIEW_REQUIRES_REMEDIATION",
        "review_result": REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "candidate_packet_outcome": CANDIDATE_PACKET_OUTCOME,
        "candidate_packet_result": CANDIDATE_PACKET_RESULT,
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
        "review_accepts_conservation_residual_candidate": True,
        "candidate_recorded_as_candidate_only": True,
        "candidate_carried_forward_exactly": True,
        "scalar_residual_carried_forward_under_selected_policy": True,
        "route_identity_carried_forward": True,
        "admissibility_only_interpretation_retained": True,
        "dynamical_action_embedding_not_assumed": True,
        "functional_embedding_packet_authorized": True,
        "functional_embedding_packet_prepared": False,
        "functional_embedding_executed": False,
        "constraint_multiplier_type_selected": False,
        "constraint_term_selected": False,
        "lambda_nu_domain_selected": False,
        "higher_derivative_scope_resolved": False,
        "boundary_terms_controlled": False,
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
            "PHI_SOURCE_ADMISSIBILITY_CK_CANDIDATE_REVIEW_ACCEPTED_"
            "NO_FUNCTIONALIZATION"
        ),
        "mathematical_statement": (
            "The review accepts the phi source-admissibility C_k candidate "
            "packet as a conservation-residual candidate only: C_source^nu[g, "
            "phi] := nabla_mu T_phi^{mu nu}, with condition C_source^nu[g, "
            "phi] = 0 and route identity C_source^nu = sum_i R_i^phi "
            "nabla^nu phi_i for R_i^phi := Box_g phi_i + partial_i V(phi). "
            "No functional embedding or C_k variation is executed."
        ),
        "non_claim_boundary": (
            "This review accepts the conservation-residual candidate only. It "
            "does not functionalize the candidate, does not embed it in S_C, "
            "does not select a multiplier type lambda_nu, does not select a "
            "constraint term, execute C_k variation, vary lambda_k, vary the "
            "candidate with respect to phi or g, claim phi generation, derive "
            "V(phi), prove new conservation, prove new source admissibility, "
            "close QFT-GR, authorize semiclassical coupling, promote the "
            "master action, claim empirical validation, or authorize public "
            "readiness. The admissibility-only interpretation is retained "
            "until the functional-embedding packet decides or blocks action "
            "embedding. It does not select or define a fully concrete C_k "
            "functional. C_k remains inactive and undefined at the fully "
            "concrete functional level, and C_k content is not fully defined. "
            "V(phi) remains smooth bounded-below but not derived. C_k does "
            "not yet generate phi. There is no ToE-native matter derivation, "
            "no native-generation theorem, no source admissibility or "
            "conservation, no QFT-GR closure, and no canonical master-action "
            "promotion."
        ),
        "critical_gate_fail_conditions": [
            "functionalize or embed the conservation residual as an action term",
            "select lambda_nu multiplier type or domain",
            "execute C_k or lambda variation",
            "execute phi or metric variation of the candidate",
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
            "ToeFormal.Derivation.PhiSourceAdmissibilityCKConstraintCandidatePacketResultReview",
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
            "candidate_packet_file": _ptr(candidate_packet_path),
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
            "Build the phi source-admissibility C_k constraint candidate "
            "packet result review."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    review = (
        build_phi_source_admissibility_ck_constraint_candidate_packet_result_review(
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
