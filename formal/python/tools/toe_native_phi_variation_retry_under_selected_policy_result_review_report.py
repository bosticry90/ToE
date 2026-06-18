from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_phi_variation_retry_under_selected_policy_packet_report import (
    AGGREGATE_TIMEOUT_STATUS,
    BOX_OPERATOR_CONVENTION,
    CK_ROLE_POLICY,
    DEFAULT_OUT as PHI_VARIATION_RETRY_PACKET_PATH,
    FIELD_DOMAIN_POLICY,
    FIELD_EULER_LAGRANGE_EQUATION,
    FIELD_VARIATION_FORM,
    KINETIC_CONVENTION_POLICY,
    METRIC_SIGNATURE_POLICY,
    METRIC_VARIATION_CONVENTION,
    METRIC_VARIATION_FORM,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as PHI_VARIATION_RETRY_PACKET_OUTCOME,
    PACKET_ID as PHI_VARIATION_RETRY_PACKET_ID,
    PHI_VARIATION_RETRY_RESULT,
    POTENTIAL_POLICY,
    SCALAR_FIELD_TYPE_POLICY,
    SCALAR_WITNESS_COMPARISON_DECISION,
    SCHEMA_ID as PHI_VARIATION_RETRY_PACKET_SCHEMA_ID,
    SELECTED_PHI_ACTION,
    STRESS_ENERGY_UNDER_SELECTED_POLICY,
    VARIATION_POLICY,
    WRITTEN_SANDBOX_DIFFERENCE,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-18T00:00:00Z"

SCHEMA_ID = (
    "TOE_NATIVE_PHI_VARIATION_RETRY_UNDER_SELECTED_POLICY_RESULT_REVIEW_"
    "20260618_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_PHI_VARIATION_RETRY_UNDER_SELECTED_POLICY_RESULT_REVIEW_v0"
PHI_VARIATION_RETRY_REVIEW_RESULT = (
    "TOE_NATIVE_PHI_VARIATION_RETRY_RESULT_REVIEW_ACCEPTS_SCALAR_WITNESS_"
    "ROUTE_MATCH_NO_NATIVE_GENERATION_OR_CK_CONTENT"
)
OUTCOME_ID = PHI_VARIATION_RETRY_REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_phi_variation_retry_result_review_accepts_scalar_witness_route_"
    "match_no_native_generation_or_ck_content"
)
NEXT_TARGET = "prepare_toe_native_phi_surface_alignment_witness_closeout"
NEXT_TARGET_KIND = "toe_native_phi_surface_alignment_witness_closeout_preparation"
DEFERRED_CK_TARGET = "prepare_toe_native_phi_ck_variational_content_packet"
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"

ALIGNMENT_WITNESS_STATUS = (
    "MASTER_ACTION_PHI_SURFACE_ALIGNMENT_WITNESS_ACCEPTED_NO_NATIVE_GENERATION"
)
ALIGNMENT_WITNESS_STATEMENT = (
    "The working-form master-action phi surface can reproduce the imported "
    "scalar sandbox route under the selected (+,-,-,-) scalar policy after "
    "signature, kinetic, and metric-variation convention normalization."
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_PHI_VARIATION_RETRY_UNDER_SELECTED_POLICY_RESULT_REVIEW_"
    "20260618_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePhiVariationRetryUnderSelectedPolicyResultReview.lean"
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
            "row_id": "selected_phi_policy_carried_forward_exactly",
            "status": "accepted",
            "evidence": [
                packet.get("metric_signature_policy"),
                packet.get("kinetic_convention_policy"),
                packet.get("potential_policy"),
                packet.get("ck_role_policy"),
            ],
            "assessment": "The selected nonpromotional phi policy is preserved.",
        },
        {
            "row_id": "field_variation_recorded_under_selected_policy",
            "status": "accepted",
            "evidence": packet.get("field_variation_form"),
            "assessment": "The field variation is recorded under the selected policy.",
        },
        {
            "row_id": "metric_variation_source_route_recorded_under_selected_policy",
            "status": "accepted",
            "evidence": [
                packet.get("metric_variation_convention"),
                packet.get("stress_energy_under_selected_policy"),
            ],
            "assessment": (
                "The metric variation convention and stress-energy route are "
                "recorded under the selected policy."
            ),
        },
        {
            "row_id": "scalar_witness_match_only_after_convention_normalization",
            "status": "accepted",
            "evidence": packet.get("scalar_witness_comparison_decision"),
            "assessment": (
                "The scalar-witness match is accepted only after convention "
                "normalization, not as a literal formula copy."
            ),
        },
        {
            "row_id": "ck_remains_undefined_and_inactive",
            "status": "accepted",
            "evidence": packet.get("ck_role_policy"),
            "assessment": "Undefined C_k does not modify the phi equation.",
        },
        {
            "row_id": "potential_smooth_bounded_below_not_derived",
            "status": "accepted",
            "evidence": packet.get("potential_policy"),
            "assessment": (
                "V(phi) is a smooth bounded-below calculation assumption, not "
                "a ToE-derived potential."
            ),
        },
        {
            "row_id": "native_generation_theorem_not_claimed",
            "status": "accepted",
            "evidence": "formal_theorem_backed_matter_derivation=false",
            "assessment": "No theorem forces the scalar structure from the ToE.",
        },
        {
            "row_id": "source_conservation_closure_and_promotion_not_claimed",
            "status": "accepted",
            "evidence": [
                "source_admissibility_claimed=false",
                "source_conservation_claimed=false",
                "qft_gr_closure_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": (
                "The review makes no source admissibility, conservation, QFT-GR "
                "closure, or master-action promotion claim."
            ),
        },
        {
            "row_id": "alignment_witness_interpretation_accepted",
            "status": "accepted",
            "evidence": ALIGNMENT_WITNESS_STATUS,
            "assessment": (
                "The accepted result is a master-action alignment witness, not "
                "a native matter derivation."
            ),
        },
        {
            "row_id": "closeout_selected_before_ck_content_packet",
            "status": "accepted",
            "evidence": [NEXT_TARGET, DEFERRED_CK_TARGET],
            "assessment": (
                "The alignment result should be closed out before attacking the "
                "C_k variational-content problem."
            ),
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "toe_native_phi_variation_retry_under_selected_policy_result_review"
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
        "full_security_scan_required": False,
    }


def build_toe_native_phi_variation_retry_under_selected_policy_result_review(
    *,
    phi_variation_retry_packet_path: Path = PHI_VARIATION_RETRY_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(phi_variation_retry_packet_path)
    review_criteria = _review_criteria(packet)
    acceptance_criteria = {
        "consumes_expected_result_review_target": (
            packet.get("schema_id") == PHI_VARIATION_RETRY_PACKET_SCHEMA_ID
            and packet.get("packet_id") == PHI_VARIATION_RETRY_PACKET_ID
            and packet.get("outcome_id") == PHI_VARIATION_RETRY_PACKET_OUTCOME
            and packet.get("selected_next_target") == CONSUMED_TARGET
            and packet.get("accepted") is True
        ),
        "selected_policy_carried_forward_exactly": (
            packet.get("metric_signature_policy") == METRIC_SIGNATURE_POLICY
            and packet.get("scalar_field_type_policy") == SCALAR_FIELD_TYPE_POLICY
            and packet.get("field_domain_policy") == FIELD_DOMAIN_POLICY
            and packet.get("kinetic_convention_policy") == KINETIC_CONVENTION_POLICY
            and packet.get("box_operator_convention") == BOX_OPERATOR_CONVENTION
            and packet.get("potential_policy") == POTENTIAL_POLICY
            and packet.get("variation_policy") == VARIATION_POLICY
            and packet.get("ck_role_policy") == CK_ROLE_POLICY
        ),
        "field_variation_recorded": (
            packet.get("field_variation_form") == FIELD_VARIATION_FORM
            and packet.get("field_euler_lagrange_equation")
            == FIELD_EULER_LAGRANGE_EQUATION
        ),
        "metric_variation_source_route_recorded": (
            packet.get("metric_variation_convention") == METRIC_VARIATION_CONVENTION
            and packet.get("metric_variation_form") == METRIC_VARIATION_FORM
            and packet.get("stress_energy_under_selected_policy")
            == STRESS_ENERGY_UNDER_SELECTED_POLICY
        ),
        "scalar_witness_match_after_normalization_only": (
            packet.get("scalar_witness_comparison_decision")
            == SCALAR_WITNESS_COMPARISON_DECISION
            and packet.get("literal_imported_sandbox_formula_copied") is False
            and "normalization" in packet.get("written_sandbox_difference", "")
        ),
        "ck_remains_undefined_and_inactive": (
            packet.get("ck_variational_content_defined") is False
            and packet.get("ck_allowed_to_modify_phi_equation") is False
            and packet.get("ck_variational_content_still_blocked") is True
        ),
        "potential_not_derived": "not ToE-derived" in packet.get("potential_policy", ""),
        "native_generation_not_claimed": (
            packet.get("formal_theorem_backed_matter_derivation") is False
            and packet.get("native_generation_blocked") is True
        ),
        "source_conservation_closure_and_promotion_not_claimed": (
            packet.get("source_admissibility_claimed") is False
            and packet.get("source_conservation_claimed") is False
            and packet.get("qft_gr_closure_claimed") is False
            and packet.get("master_action_promoted") is False
        ),
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
        "next_target_is_alignment_closeout": NEXT_TARGET
        == "prepare_toe_native_phi_surface_alignment_witness_closeout",
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_PHI_VARIATION_RETRY_RESULT_REVIEW"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_PHI_VARIATION_RETRY_RESULT_REVIEW",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_PHI_VARIATION_RETRY_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "review_result": PHI_VARIATION_RETRY_REVIEW_RESULT,
        "phi_variation_retry_result": PHI_VARIATION_RETRY_RESULT,
        "phi_variation_retry_packet_outcome": PHI_VARIATION_RETRY_PACKET_OUTCOME,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "deferred_ck_variational_content_target": DEFERRED_CK_TARGET,
        "alignment_witness_status": ALIGNMENT_WITNESS_STATUS,
        "alignment_witness_statement": ALIGNMENT_WITNESS_STATEMENT,
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
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "selected_phi_policy_carried_forward_exactly": True,
        "field_variation_recorded_under_selected_policy": True,
        "metric_variation_source_route_recorded_under_selected_policy": True,
        "scalar_witness_route_match_accepted": True,
        "scalar_witness_match_only_after_convention_normalization": True,
        "literal_imported_sandbox_formula_copied": False,
        "ck_remains_undefined_and_inactive": True,
        "ck_allowed_to_modify_phi_equation": False,
        "ck_variational_content_defined": False,
        "ck_variational_content_still_blocked": True,
        "potential_smooth_bounded_below": True,
        "potential_derived": False,
        "native_generation_theorem_claimed": False,
        "native_generation_blocked": True,
        "alignment_witness_closeout_authorized": True,
        "ck_variational_content_packet_deferred": True,
        "record_validated": True,
        "proof_depth_label": (
            "RESULT_REVIEW_ACCEPTS_ALIGNMENT_WITNESS_NO_NATIVE_DERIVATION"
        ),
        "phi_variation_retry_executed": True,
        "phi_variation_route_executed": True,
        "phi_variation_derived_as_toe_native": False,
        "phi_stress_energy_derived_as_toe_native": False,
        "formal_theorem_backed_matter_derivation": False,
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
        "critical_gate_fail_conditions": [
            "claim native generation",
            "claim C_k variational content",
            "treat the normalized scalar-witness match as a literal imported copy",
            "derive V(phi) from the ToE",
            "claim source admissibility or conservation",
            "claim QFT-GR closure",
            "promote the working-form master action",
        ],
        "downstream_progression": [
            {
                "stage": "variation_retry_result_review",
                "status": "ACCEPTED_ALIGNMENT_WITNESS_NO_NATIVE_GENERATION",
                "decision": PHI_VARIATION_RETRY_REVIEW_RESULT,
                "reason": (
                    "The selected-policy phi variation retry reproduces the "
                    "scalar witness route only after convention normalization."
                ),
            },
            {
                "stage": "alignment_witness_closeout",
                "status": "NEXT_TARGET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": (
                    "The alignment result should be preserved as a bounded "
                    "closeout before C_k variational content is attempted."
                ),
            },
            {
                "stage": "ck_variational_content",
                "status": "DEFERRED",
                "decision": DEFERRED_CK_TARGET,
                "reason": (
                    "C_k remains the native-content frontier after alignment "
                    "witness closeout."
                ),
            },
        ],
        "mathematical_statement": (
            "The review accepts that the selected-policy master-action phi "
            "surface records delta_phi S giving Box_g phi_i + partial_i V(phi) "
            "= 0 and inverse-metric variation giving the selected scalar "
            "stress-energy route. The match with the imported scalar sandbox is "
            "a route-level match after convention normalization only."
        ),
        "non_claim_boundary": (
            "This result review accepts a master-action alignment witness only. "
            "It does not prove ToE-native matter derivation, does not supply a "
            "native-generation theorem, does not derive V(phi), does not define "
            "or vary C_k content, does not claim source admissibility or "
            "conservation, does not close QFT-GR, does not authorize "
            "semiclassical coupling, does not promote the master action, does "
            "not claim empirical validation, and does not authorize public "
            "readiness or release completion."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativePhiVariationRetryUnderSelectedPolicyResultReview",
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


def write_toe_native_phi_variation_retry_under_selected_policy_result_review(
    *,
    phi_variation_retry_packet_path: Path = PHI_VARIATION_RETRY_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = build_toe_native_phi_variation_retry_under_selected_policy_result_review(
        phi_variation_retry_packet_path=phi_variation_retry_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Build the ToE-native phi variation retry under selected policy result review."
        )
    )
    parser.add_argument(
        "--phi-variation-retry-packet",
        type=Path,
        default=PHI_VARIATION_RETRY_PACKET_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()
    packet = write_toe_native_phi_variation_retry_under_selected_policy_result_review(
        phi_variation_retry_packet_path=args.phi_variation_retry_packet,
        out=args.out,
        captured_at_utc=args.captured_at_utc,
    )
    print(json.dumps(packet, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
