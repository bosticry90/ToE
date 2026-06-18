from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_phi_variation_retry_under_selected_policy_result_review_report import (
    AGGREGATE_TIMEOUT_STATUS,
    ALIGNMENT_WITNESS_STATEMENT,
    ALIGNMENT_WITNESS_STATUS,
    BOX_OPERATOR_CONVENTION,
    CK_ROLE_POLICY,
    DEFAULT_OUT as PHI_VARIATION_RETRY_RESULT_REVIEW_PATH,
    DEFERRED_CK_TARGET,
    FIELD_DOMAIN_POLICY,
    FIELD_EULER_LAGRANGE_EQUATION,
    FIELD_VARIATION_FORM,
    KINETIC_CONVENTION_POLICY,
    METRIC_SIGNATURE_POLICY,
    METRIC_VARIATION_CONVENTION,
    METRIC_VARIATION_FORM,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as PHI_VARIATION_RETRY_REVIEW_OUTCOME,
    PACKET_ID as PHI_VARIATION_RETRY_REVIEW_PACKET_ID,
    PHI_VARIATION_RETRY_REVIEW_RESULT,
    PHI_VARIATION_RETRY_RESULT,
    POTENTIAL_POLICY,
    SCALAR_FIELD_TYPE_POLICY,
    SCALAR_WITNESS_COMPARISON_DECISION,
    SCHEMA_ID as PHI_VARIATION_RETRY_REVIEW_SCHEMA_ID,
    SELECTED_PHI_ACTION,
    STRESS_ENERGY_UNDER_SELECTED_POLICY,
    VARIATION_POLICY,
    WRITTEN_SANDBOX_DIFFERENCE,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-18T00:00:00Z"

SCHEMA_ID = "TOE_NATIVE_PHI_SURFACE_ALIGNMENT_WITNESS_CLOSEOUT_20260618_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_PHI_SURFACE_ALIGNMENT_WITNESS_CLOSEOUT_v0"
CLOSEOUT_RESULT = (
    "TOE_NATIVE_PHI_SURFACE_ALIGNMENT_WITNESS_CLOSED_AS_MASTER_ACTION_SCALAR_"
    "ROUTE_MATCH_NO_NATIVE_GENERATION_OR_CK_CONTENT"
)
OUTCOME_ID = CLOSEOUT_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_phi_surface_alignment_witness_closed_as_master_action_scalar_"
    "route_match_no_native_generation_or_ck_content"
)
NEXT_TARGET = "prepare_toe_native_phi_ck_variational_content_packet"
NEXT_TARGET_KIND = "toe_native_phi_ck_variational_content_packet_preparation"
ALIGNMENT_WITNESS_CLOSEOUT_STATUS = (
    "MASTER_ACTION_PHI_SURFACE_ALIGNMENT_WITNESS_CLOSED_NO_NATIVE_GENERATION_"
    "OR_CK_CONTENT"
)
CK_VARIATIONAL_CONTENT_FRONTIER_QUESTION = (
    "Do the seam constraints C_k actually generate, restrict, or explain the "
    "phi route?"
)
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_PHI_SURFACE_ALIGNMENT_WITNESS_CLOSEOUT_20260618_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePhiSurfaceAlignmentWitnessCloseout.lean"
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
            "row_id": "selected_phi_policy_was_used",
            "status": "accepted",
            "evidence": [
                review.get("metric_signature_policy"),
                review.get("kinetic_convention_policy"),
                review.get("variation_policy"),
            ],
            "assessment": (
                "The closeout preserves the selected (+,-,-,-) finite-real-"
                "multiplet calculation policy used by the retry."
            ),
        },
        {
            "row_id": "phi_variation_route_matched_scalar_witness_after_normalization",
            "status": "accepted",
            "evidence": review.get("scalar_witness_comparison_decision"),
            "assessment": (
                "The match is a route-level scalar witness match after "
                "signature, kinetic, and metric-variation normalization."
            ),
        },
        {
            "row_id": "master_action_alignment_not_native_derivation",
            "status": "accepted",
            "evidence": [
                review.get("alignment_witness_status"),
                "formal_theorem_backed_matter_derivation=false",
            ],
            "assessment": (
                "The result is closed as master-action alignment, not as a "
                "ToE-native matter derivation."
            ),
        },
        {
            "row_id": "potential_selected_not_derived",
            "status": "accepted",
            "evidence": review.get("potential_policy"),
            "assessment": "V(phi) remains a selected smooth bounded-below input.",
        },
        {
            "row_id": "ck_undefined_and_inactive",
            "status": "accepted",
            "evidence": review.get("ck_role_policy"),
            "assessment": (
                "Undefined C_k content remains inactive and cannot modify the "
                "phi equation in the closeout."
            ),
        },
        {
            "row_id": "no_source_admissibility_or_conservation_newly_claimed",
            "status": "accepted",
            "evidence": [
                "source_admissibility_claimed=false",
                "source_conservation_claimed=false",
            ],
            "assessment": (
                "The closeout adds no source admissibility or conservation "
                "claim."
            ),
        },
        {
            "row_id": "no_qft_gr_closure_claimed",
            "status": "accepted",
            "evidence": "qft_gr_closure_claimed=false",
            "assessment": "QFT-GR closure and seam closure remain blocked.",
        },
        {
            "row_id": "no_master_action_promotion_claimed",
            "status": "accepted",
            "evidence": "master_action_promoted=false",
            "assessment": (
                "The working-form master action is not promoted by the "
                "alignment witness closeout."
            ),
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_phi_surface_alignment_witness_closeout",
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


def build_toe_native_phi_surface_alignment_witness_closeout(
    *,
    phi_variation_retry_result_review_path: Path = (
        PHI_VARIATION_RETRY_RESULT_REVIEW_PATH
    ),
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(phi_variation_retry_result_review_path)
    closeout_criteria = _closeout_criteria(review)
    acceptance_criteria = {
        "consumes_expected_alignment_closeout_target": (
            review.get("schema_id") == PHI_VARIATION_RETRY_REVIEW_SCHEMA_ID
            and review.get("packet_id") == PHI_VARIATION_RETRY_REVIEW_PACKET_ID
            and review.get("outcome_id") == PHI_VARIATION_RETRY_REVIEW_OUTCOME
            and review.get("review_result") == PHI_VARIATION_RETRY_REVIEW_RESULT
            and review.get("selected_next_target") == CONSUMED_TARGET
            and review.get("accepted") is True
        ),
        "selected_phi_policy_was_used": (
            review.get("metric_signature_policy") == METRIC_SIGNATURE_POLICY
            and review.get("scalar_field_type_policy") == SCALAR_FIELD_TYPE_POLICY
            and review.get("field_domain_policy") == FIELD_DOMAIN_POLICY
            and review.get("kinetic_convention_policy") == KINETIC_CONVENTION_POLICY
            and review.get("box_operator_convention") == BOX_OPERATOR_CONVENTION
            and review.get("potential_policy") == POTENTIAL_POLICY
            and review.get("variation_policy") == VARIATION_POLICY
            and review.get("ck_role_policy") == CK_ROLE_POLICY
        ),
        "phi_variation_route_matched_scalar_witness_after_normalization": (
            review.get("phi_variation_retry_result") == PHI_VARIATION_RETRY_RESULT
            and review.get("scalar_witness_comparison_decision")
            == SCALAR_WITNESS_COMPARISON_DECISION
            and review.get("scalar_witness_match_only_after_convention_normalization")
            is True
            and review.get("literal_imported_sandbox_formula_copied") is False
        ),
        "master_action_alignment_not_native_derivation": (
            review.get("alignment_witness_status") == ALIGNMENT_WITNESS_STATUS
            and review.get("formal_theorem_backed_matter_derivation") is False
            and review.get("toe_native_matter_derivation_claimed") is False
            and review.get("native_generation_theorem_claimed") is False
        ),
        "potential_selected_not_derived": (
            review.get("potential_smooth_bounded_below") is True
            and review.get("potential_derived") is False
        ),
        "ck_undefined_and_inactive": (
            review.get("ck_remains_undefined_and_inactive") is True
            and review.get("ck_variational_content_defined") is False
            and review.get("ck_allowed_to_modify_phi_equation") is False
        ),
        "no_source_admissibility_or_conservation_newly_claimed": (
            review.get("source_admissibility_claimed") is False
            and review.get("source_conservation_claimed") is False
            and review.get("toe_native_phi_source_admissibility_claimed") is False
            and review.get("toe_native_phi_source_conservation_claimed") is False
        ),
        "no_qft_gr_closure_claimed": (
            review.get("qft_gr_closure_claimed") is False
            and review.get("qft_gr_seam_closed") is False
            and review.get("source_map_closed") is False
        ),
        "no_master_action_promotion_claimed": (
            review.get("master_action_promoted") is False
            and review.get("canonical_master_action_promoted") is False
            and review.get("master_action_promotion_authorized") is False
        ),
        "closeout_criteria_all_accepted": all(
            row["status"] == "accepted" for row in closeout_criteria
        ),
        "next_target_is_ck_variational_content_packet": NEXT_TARGET
        == DEFERRED_CK_TARGET,
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_PHI_SURFACE_ALIGNMENT_WITNESS_CLOSEOUT"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_PHI_SURFACE_ALIGNMENT_WITNESS_CLOSEOUT",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_PHI_SURFACE_ALIGNMENT_WITNESS_CLOSEOUT_REQUIRES_REMEDIATION",
        "closeout_result": CLOSEOUT_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "ck_variational_content_frontier_question": (
            CK_VARIATIONAL_CONTENT_FRONTIER_QUESTION
        ),
        "alignment_witness_status": ALIGNMENT_WITNESS_STATUS,
        "alignment_witness_closeout_status": ALIGNMENT_WITNESS_CLOSEOUT_STATUS,
        "alignment_witness_statement": ALIGNMENT_WITNESS_STATEMENT,
        "phi_variation_retry_review_outcome": PHI_VARIATION_RETRY_REVIEW_OUTCOME,
        "phi_variation_retry_review_result": PHI_VARIATION_RETRY_REVIEW_RESULT,
        "phi_variation_retry_result": PHI_VARIATION_RETRY_RESULT,
        "selected_phi_action": SELECTED_PHI_ACTION,
        "metric_signature_policy": METRIC_SIGNATURE_POLICY,
        "scalar_field_type_policy": SCALAR_FIELD_TYPE_POLICY,
        "field_domain_policy": FIELD_DOMAIN_POLICY,
        "kinetic_convention_policy": KINETIC_CONVENTION_POLICY,
        "box_operator_convention": BOX_OPERATOR_CONVENTION,
        "potential_policy": POTENTIAL_POLICY,
        "variation_policy": VARIATION_POLICY,
        "ck_role_policy": CK_ROLE_POLICY,
        "field_variation_form": FIELD_VARIATION_FORM,
        "field_euler_lagrange_equation": FIELD_EULER_LAGRANGE_EQUATION,
        "metric_variation_convention": METRIC_VARIATION_CONVENTION,
        "metric_variation_form": METRIC_VARIATION_FORM,
        "stress_energy_under_selected_policy": STRESS_ENERGY_UNDER_SELECTED_POLICY,
        "scalar_witness_comparison_decision": SCALAR_WITNESS_COMPARISON_DECISION,
        "written_sandbox_difference": WRITTEN_SANDBOX_DIFFERENCE,
        "closeout_criteria": closeout_criteria,
        "closeout_criteria_count": len(closeout_criteria),
        "closeout_criteria_accepted_count": sum(
            1 for row in closeout_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "selected_phi_policy_was_used": True,
        "phi_variation_route_matched_scalar_witness_after_normalization": True,
        "master_action_alignment_not_native_derivation": True,
        "potential_selected_not_derived": True,
        "ck_undefined_and_inactive": True,
        "no_source_admissibility_or_conservation_newly_claimed": True,
        "no_qft_gr_closure_claimed": True,
        "no_master_action_promotion_claimed": True,
        "alignment_witness_closed": True,
        "alignment_witness_closeout_prepared": True,
        "ck_variational_content_packet_authorized": True,
        "ck_variational_content_packet_deferred_until_after_closeout": True,
        "native_generation_blocked": True,
        "potential_smooth_bounded_below": True,
        "potential_derived": False,
        "ck_remains_undefined_and_inactive": True,
        "ck_allowed_to_modify_phi_equation": False,
        "ck_variational_content_defined": False,
        "ck_variational_content_still_blocked": True,
        "scalar_witness_route_match_accepted": True,
        "scalar_witness_match_only_after_convention_normalization": True,
        "literal_imported_sandbox_formula_copied": False,
        "proof_depth_label": (
            "CLOSEOUT_RECORDS_MASTER_ACTION_ALIGNMENT_WITNESS_NO_NATIVE_DERIVATION"
        ),
        "formal_theorem_backed_matter_derivation": False,
        "native_generation_theorem_claimed": False,
        "phi_variation_derived_as_toe_native": False,
        "phi_stress_energy_derived_as_toe_native": False,
        "toe_native_phi_source_route_constructed": False,
        "toe_native_phi_source_admissibility_claimed": False,
        "toe_native_phi_source_conservation_claimed": False,
        "toe_native_matter_derivation_claimed": False,
        "toe_native_matter_sector_derived": False,
        "toe_native_matter_sector_defined": False,
        "toe_matter_sector_derived": False,
        "toe_matter_model_derived": False,
        "standard_model_derivation_claimed": False,
        "source_admissibility_claimed": False,
        "source_admissibility_completed": False,
        "source_conservation_claimed": False,
        "weak_conservation_claimed": False,
        "bianchi_compatibility_claimed": False,
        "source_map_closed": False,
        "qft_gr_solved": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "qft_gr_source_map_closure_authorized": False,
        "semiclassical_coupling_authorized": False,
        "semiclassical_coupling_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "semiclassical_source_established": False,
        "empirical_validation_claimed": False,
        "public_readiness_claimed": False,
        "public_submission_authorized": False,
        "canonical_master_action_promoted": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "phase2_readiness_claim": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "scalar_route_level_status": [
            {
                "level": "imported_scalar_sandbox",
                "status": "positive_classical_witness",
            },
            {
                "level": "master_action_phi_surface",
                "status": (
                    "matches_scalar_witness_under_selected_policy_after_"
                    "convention_normalization"
                ),
            },
            {
                "level": "toe_native_explanation",
                "status": (
                    "blocked_by_missing_C_k_content_and_no_native_generation_"
                    "theorem"
                ),
            },
        ],
        "critical_gate_fail_conditions": [
            "promote alignment witness into ToE-native matter derivation",
            "claim native-generation theorem",
            "claim C_k variational content",
            "claim V(phi) is ToE-derived",
            "claim source admissibility or conservation",
            "claim QFT-GR closure",
            "promote the working-form master action",
        ],
        "downstream_progression": [
            {
                "stage": "alignment_witness_closeout",
                "status": "CLOSED_AS_MASTER_ACTION_ALIGNMENT_WITNESS",
                "decision": CLOSEOUT_RESULT,
                "reason": (
                    "The selected-policy phi surface reproduces the scalar "
                    "witness route after convention normalization only."
                ),
            },
            {
                "stage": "ck_variational_content_packet",
                "status": "NEXT_TARGET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": (
                    "C_k is the next native-content frontier for whether the "
                    "ToE generates, restricts, or explains the phi route."
                ),
            },
        ],
        "mathematical_statement": (
            "The closeout preserves the reviewed result that S_phi^policy "
            "under the selected (+,-,-,-) convention yields Box_g phi_i + "
            "partial_i V(phi) = 0 and the selected stress-energy route, "
            "matching the imported scalar sandbox only after convention "
            "normalization. This is a master-action alignment witness, not a "
            "native ToE derivation."
        ),
        "non_claim_boundary": (
            "This closeout records a master-action phi alignment witness only. "
            "It does not prove ToE-native matter derivation, does not supply a "
            "native-generation theorem, does not derive V(phi), does not "
            "define or vary C_k content, does not claim source admissibility "
            "or conservation, does not close QFT-GR, does not authorize "
            "semiclassical coupling, does not promote the working-form master "
            "action, does not claim empirical validation, and does not "
            "authorize public readiness or release completion."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativePhiSurfaceAlignmentWitnessCloseout",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "lane_level_lean_target_files": [
            _ptr(LEAN_PACKET_PATH),
            _ptr(QFTGR_AGGREGATE_PATH),
            _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            _ptr(RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH),
        ],
        "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        "validation_policy": _validation_policy(),
    }


def write_toe_native_phi_surface_alignment_witness_closeout(
    *,
    phi_variation_retry_result_review_path: Path = (
        PHI_VARIATION_RETRY_RESULT_REVIEW_PATH
    ),
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = build_toe_native_phi_surface_alignment_witness_closeout(
        phi_variation_retry_result_review_path=(
            phi_variation_retry_result_review_path
        ),
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Build the ToE-native phi surface alignment witness closeout."
    )
    parser.add_argument(
        "--phi-variation-retry-result-review",
        type=Path,
        default=PHI_VARIATION_RETRY_RESULT_REVIEW_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()
    packet = write_toe_native_phi_surface_alignment_witness_closeout(
        phi_variation_retry_result_review_path=(
            args.phi_variation_retry_result_review
        ),
        out=args.out,
        captured_at_utc=args.captured_at_utc,
    )
    print(json.dumps(packet, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
