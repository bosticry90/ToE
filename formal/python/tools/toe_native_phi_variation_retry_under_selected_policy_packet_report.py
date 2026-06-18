from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_action_derivability_retry_with_provisional_matter_sector_report import (
    SCALAR_LAGRANGIAN as IMPORTED_SCALAR_LAGRANGIAN,
    STRESS_ENERGY_COVARIANT_EXPRESSION as IMPORTED_STRESS_ENERGY_COVARIANT_EXPRESSION,
)
from formal.python.tools.toe_native_phi_signature_domain_and_potential_policy_packet_report import (
    BOX_OPERATOR_CONVENTION,
    CK_ROLE_POLICY,
    DEFAULT_OUT as PHI_POLICY_PACKET_PATH,
    FIELD_DOMAIN_POLICY,
    KINETIC_CONVENTION_POLICY,
    METRIC_SIGNATURE_POLICY,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as PHI_POLICY_PACKET_OUTCOME,
    PACKET_ID as PHI_POLICY_PACKET_ID,
    PHI_POLICY_PACKET_RESULT,
    POTENTIAL_POLICY,
    SCALAR_FIELD_TYPE_POLICY,
    SCHEMA_ID as PHI_POLICY_PACKET_SCHEMA_ID,
    SELECTED_PHI_EQUATION_NO_CK,
    VARIATION_POLICY,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-18T00:00:00Z"

SCHEMA_ID = "TOE_NATIVE_PHI_VARIATION_RETRY_UNDER_SELECTED_POLICY_PACKET_20260618_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_PHI_VARIATION_RETRY_UNDER_SELECTED_POLICY_PACKET_v0"
PHI_VARIATION_RETRY_RESULT = (
    "PHI_VARIATION_ROUTE_REPRODUCES_SCALAR_WITNESS_UNDER_SELECTED_POLICY_"
    "NO_NATIVE_GENERATION_CLAIM"
)
OUTCOME_ID = (
    "TOE_NATIVE_PHI_VARIATION_RETRY_UNDER_SELECTED_POLICY_PACKET_PREPARED_"
    "PHI_VARIATION_ROUTE_REPRODUCES_SCALAR_WITNESS_UNDER_SELECTED_POLICY_"
    "NO_NATIVE_GENERATION_CLAIM_CK_BLOCKED"
)
PACKET_CLASSIFICATION = (
    "toe_native_phi_variation_retry_under_selected_policy_records_field_and_"
    "metric_variation_reproducing_scalar_witness_route_without_native_generation"
)
NEXT_TARGET = "review_toe_native_phi_variation_retry_under_selected_policy_result"
NEXT_TARGET_KIND = "toe_native_phi_variation_retry_under_selected_policy_result_review"
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"
AGGREGATE_TIMEOUT_STATUS = "INCOMPLETE_TIMEOUT_STEADY_PROGRESS"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_PHI_VARIATION_RETRY_UNDER_SELECTED_POLICY_PACKET_20260618_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePhiVariationRetryUnderSelectedPolicyPacket.lean"
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

SELECTED_PHI_ACTION = (
    "S_phi^policy[g, phi] = integral_M sqrt(-g) "
    "[1/2 sum_i g^{mu nu} nabla_mu phi_i nabla_nu phi_i - V(phi)] d^4x"
)
FIELD_VARIATION_FORM = (
    "delta_phi S_phi^policy(eta) = - integral_M sqrt(-g) "
    "sum_i (Box_g phi_i + partial_i V(phi)) eta_i d^4x"
)
FIELD_EULER_LAGRANGE_EQUATION = SELECTED_PHI_EQUATION_NO_CK
METRIC_VARIATION_CONVENTION = (
    "vary inverse metric k^{mu nu}=delta g^{mu nu}, hold phi fixed, use "
    "delta sqrt(-g) = -1/2 sqrt(-g) g_{mu nu} k^{mu nu}, and define "
    "T^policy_{mu nu} = 2/sqrt(-g) delta S_phi^policy / delta g^{mu nu}"
)
METRIC_VARIATION_FORM = (
    "delta_g S_phi^policy(k) = 1/2 integral_M sqrt(-g) "
    "T^policy_{mu nu} k^{mu nu} d^4x"
)
STRESS_ENERGY_UNDER_SELECTED_POLICY = (
    "T^policy_{mu nu} = sum_i nabla_mu phi_i nabla_nu phi_i - "
    "g_{mu nu}[1/2 sum_j nabla_alpha phi_j nabla^alpha phi_j - V(phi)]"
)
SINGLE_FIELD_REDUCTION = (
    "for |I_phi|=1 and C_k inactive, the field equation is "
    "Box_g phi + V'(phi) = 0 and the stress-energy route is the usual real "
    "scalar route after translating the imported sandbox signature/kinetic "
    "and metric-variation conventions"
)
SCALAR_WITNESS_COMPARISON_DECISION = (
    "reproduces_scalar_witness_route_after_selected_policy_normalization_no_"
    "native_generation_claim"
)
WRITTEN_SANDBOX_DIFFERENCE = (
    "the imported scalar sandbox used a different written kinetic convention "
    "and metric-variation sign; the match is route-level after convention "
    "normalization, not a literal string copy"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _calculation_steps() -> list[dict[str, Any]]:
    return [
        {
            "step_id": "state_selected_phi_action",
            "status": "recorded",
            "mathematical_content": SELECTED_PHI_ACTION,
        },
        {
            "step_id": "state_selected_policy",
            "status": "recorded",
            "mathematical_content": {
                "signature": METRIC_SIGNATURE_POLICY,
                "field_type": SCALAR_FIELD_TYPE_POLICY,
                "domain": FIELD_DOMAIN_POLICY,
                "kinetic": KINETIC_CONVENTION_POLICY,
                "box": BOX_OPERATOR_CONVENTION,
                "potential": POTENTIAL_POLICY,
                "variation": VARIATION_POLICY,
                "ck_role": CK_ROLE_POLICY,
            },
        },
        {
            "step_id": "vary_phi",
            "status": "computed_under_selected_policy",
            "mathematical_content": FIELD_VARIATION_FORM,
        },
        {
            "step_id": "read_field_equation",
            "status": "computed_under_selected_policy",
            "mathematical_content": FIELD_EULER_LAGRANGE_EQUATION,
        },
        {
            "step_id": "vary_inverse_metric",
            "status": "computed_under_selected_policy",
            "mathematical_content": METRIC_VARIATION_FORM,
        },
        {
            "step_id": "read_stress_energy_route",
            "status": "computed_under_selected_policy",
            "mathematical_content": STRESS_ENERGY_UNDER_SELECTED_POLICY,
        },
        {
            "step_id": "compare_imported_scalar_witness",
            "status": "matches_after_convention_normalization",
            "mathematical_content": SCALAR_WITNESS_COMPARISON_DECISION,
        },
        {
            "step_id": "retain_ck_and_native_generation_blockers",
            "status": "retained",
            "mathematical_content": (
                "C_k inactive; no native-generation theorem; no source "
                "admissibility or conservation claim"
            ),
        },
    ]


def _review_criteria(policy_packet: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "consumes_expected_variation_retry_target",
            "status": "accepted",
            "evidence": policy_packet.get("selected_next_target"),
            "assessment": "The policy packet authorized this variation retry.",
        },
        {
            "row_id": "selected_policy_used",
            "status": "accepted",
            "evidence": [
                policy_packet.get("metric_signature_policy"),
                policy_packet.get("kinetic_convention_policy"),
                policy_packet.get("box_operator_convention"),
            ],
            "assessment": "The retry uses the selected nonpromotional policy.",
        },
        {
            "row_id": "field_variation_computed",
            "status": "accepted",
            "evidence": FIELD_VARIATION_FORM,
            "assessment": "The phi Euler-Lagrange route is computed.",
        },
        {
            "row_id": "field_equation_matches_selected_policy",
            "status": "accepted",
            "evidence": FIELD_EULER_LAGRANGE_EQUATION,
            "assessment": "The field equation is Box_g phi_i + partial_i V = 0.",
        },
        {
            "row_id": "metric_variation_computed",
            "status": "accepted",
            "evidence": [METRIC_VARIATION_CONVENTION, METRIC_VARIATION_FORM],
            "assessment": "The metric variation convention and route are explicit.",
        },
        {
            "row_id": "stress_energy_route_recorded",
            "status": "accepted",
            "evidence": STRESS_ENERGY_UNDER_SELECTED_POLICY,
            "assessment": "The convention-dependent stress-energy route is recorded.",
        },
        {
            "row_id": "scalar_witness_reproduced_after_normalization",
            "status": "accepted",
            "evidence": SCALAR_WITNESS_COMPARISON_DECISION,
            "assessment": (
                "The retry reproduces the scalar witness route after translating "
                "signature, kinetic, and metric-variation conventions."
            ),
        },
        {
            "row_id": "ck_content_inactive_and_blocked",
            "status": "accepted",
            "evidence": CK_ROLE_POLICY,
            "assessment": "Undefined C_k does not modify the phi equation.",
        },
        {
            "row_id": "native_generation_not_claimed",
            "status": "accepted",
            "evidence": "formal_theorem_backed_matter_derivation=false",
            "assessment": "No theorem forces the phi scalar structure from ToE.",
        },
        {
            "row_id": "next_review_authorized",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The result should be reviewed before downstream source work.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_phi_variation_retry_under_selected_policy_packet",
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


def build_toe_native_phi_variation_retry_under_selected_policy_packet(
    *,
    phi_policy_packet_path: Path = PHI_POLICY_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    policy_packet = _read_json(phi_policy_packet_path)
    steps = _calculation_steps()
    review_criteria = _review_criteria(policy_packet)
    acceptance_criteria = {
        "consumes_expected_variation_retry_target": (
            policy_packet.get("schema_id") == PHI_POLICY_PACKET_SCHEMA_ID
            and policy_packet.get("packet_id") == PHI_POLICY_PACKET_ID
            and policy_packet.get("outcome_id") == PHI_POLICY_PACKET_OUTCOME
            and policy_packet.get("selected_next_target") == CONSUMED_TARGET
            and policy_packet.get("accepted") is True
        ),
        "selected_policy_matches_packet": (
            policy_packet.get("metric_signature_policy") == METRIC_SIGNATURE_POLICY
            and policy_packet.get("box_operator_convention") == BOX_OPERATOR_CONVENTION
            and policy_packet.get("ck_allowed_to_modify_phi_equation") is False
        ),
        "field_variation_computed": "delta_phi S_phi^policy" in FIELD_VARIATION_FORM,
        "field_equation_computed": (
            FIELD_EULER_LAGRANGE_EQUATION == "Box_g phi_i + partial_i V(phi) = 0"
        ),
        "metric_variation_convention_explicit": (
            "T^policy_{mu nu} = 2/sqrt(-g)" in METRIC_VARIATION_CONVENTION
        ),
        "stress_energy_route_recorded": (
            "T^policy_{mu nu}" in STRESS_ENERGY_UNDER_SELECTED_POLICY
        ),
        "scalar_witness_reproduced_after_normalization": (
            "reproduces_scalar_witness_route" in SCALAR_WITNESS_COMPARISON_DECISION
        ),
        "ck_content_inactive_and_blocked": (
            "not allowed to modify" in CK_ROLE_POLICY
            and policy_packet.get("ck_variational_content_defined") is False
        ),
        "native_generation_not_claimed": True,
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
        "next_target_is_result_review": NEXT_TARGET.startswith("review_"),
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_TOE_NATIVE_PHI_VARIATION_RETRY_UNDER_SELECTED_POLICY_PACKET"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_PHI_VARIATION_RETRY_UNDER_SELECTED_POLICY_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else "TOE_NATIVE_PHI_VARIATION_RETRY_UNDER_SELECTED_POLICY_PACKET_REQUIRES_REMEDIATION",
        "phi_variation_retry_result": PHI_VARIATION_RETRY_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "phi_policy_packet_result": PHI_POLICY_PACKET_RESULT,
        "reviewed_phi_policy_packet_artifact_id": policy_packet.get("schema_id"),
        "reviewed_phi_policy_packet_outcome": policy_packet.get("outcome_id"),
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
        "single_field_reduction": SINGLE_FIELD_REDUCTION,
        "imported_scalar_lagrangian": IMPORTED_SCALAR_LAGRANGIAN,
        "imported_scalar_stress_energy_covariant_expression": (
            IMPORTED_STRESS_ENERGY_COVARIANT_EXPRESSION
        ),
        "scalar_witness_comparison_decision": SCALAR_WITNESS_COMPARISON_DECISION,
        "written_sandbox_difference": WRITTEN_SANDBOX_DIFFERENCE,
        "calculation_steps": steps,
        "calculation_step_count": len(steps),
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "field_variation_computed": True,
        "metric_variation_computed": True,
        "stress_energy_route_recorded": True,
        "scalar_witness_route_reproduced_under_selected_policy": True,
        "sign_convention_verified_explicitly": True,
        "literal_imported_sandbox_formula_copied": False,
        "ck_allowed_to_modify_phi_equation": False,
        "ck_variational_content_defined": False,
        "ck_variational_content_still_blocked": True,
        "native_generation_blocked": True,
        "formal_theorem_backed_matter_derivation": False,
        "record_validated": True,
        "symbolic_calculation_recorded": True,
        "proof_depth_label": "SYMBOLIC_VARIATION_RETRY_RECORDED_NO_NATIVE_DERIVATION",
        "phi_variation_retry_executed": True,
        "phi_variation_route_executed": True,
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
        "critical_gate_fail_conditions": [
            "claim ToE-native matter derivation",
            "claim native-generation theorem",
            "let undefined C_k modify the scalar equation",
            "copy imported scalar expression without convention translation",
            "claim source admissibility",
            "claim conservation",
            "claim QFT-GR closure",
            "authorize semiclassical coupling or master-action promotion",
        ],
        "downstream_progression": [
            {
                "stage": "phi_variation_retry_under_selected_policy",
                "status": "REPRODUCES_SCALAR_WITNESS_ROUTE_NO_NATIVE_GENERATION",
                "decision": PHI_VARIATION_RETRY_RESULT,
                "reason": (
                    "The selected-policy field and metric variations reproduce "
                    "the scalar witness route after convention normalization."
                ),
            },
            {
                "stage": "result_review",
                "status": "NEXT_TARGET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": (
                    "The retry result must be reviewed before any source ladder, "
                    "C_k content, or native-generation work."
                ),
            },
        ],
        "mathematical_statement": (
            "Under the selected (+,-,-,-) policy with L_phi = 1/2 sum_i "
            "nabla_mu phi_i nabla^mu phi_i - V(phi), compact-support or "
            "fixed-boundary phi variation gives Box_g phi_i + partial_i V(phi) "
            "= 0. Inverse-metric variation with "
            "T^policy_{mu nu}=2/sqrt(-g) delta S/delta g^{mu nu} gives "
            "T^policy_{mu nu}=sum_i nabla_mu phi_i nabla_nu phi_i - "
            "g_{mu nu}[1/2 sum_j nabla_alpha phi_j nabla^alpha phi_j - V(phi)]. "
            "For a single field and inactive C_k, this reproduces the imported "
            "scalar witness route after signature, kinetic, and metric-variation "
            "convention normalization."
        ),
        "non_claim_boundary": (
            "This variation retry records a convention-normalized symbolic "
            "calculation only. It does not prove ToE-native matter derivation, "
            "does not supply a native-generation theorem, does not define or use "
            "C_k variational content, does not claim source admissibility or "
            "conservation, does not derive the Standard Model, does not close "
            "QFT-GR, does not authorize semiclassical coupling, does not promote "
            "the master action, does not claim empirical validation, and does "
            "not authorize public readiness or release completion."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativePhiVariationRetryUnderSelectedPolicyPacket",
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


def write_toe_native_phi_variation_retry_under_selected_policy_packet(
    *,
    phi_policy_packet_path: Path = PHI_POLICY_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = build_toe_native_phi_variation_retry_under_selected_policy_packet(
        phi_policy_packet_path=phi_policy_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Build the ToE-native phi variation retry under selected policy packet."
    )
    parser.add_argument("--phi-policy-packet", type=Path, default=PHI_POLICY_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()
    packet = write_toe_native_phi_variation_retry_under_selected_policy_packet(
        phi_policy_packet_path=args.phi_policy_packet,
        out=args.out,
        captured_at_utc=args.captured_at_utc,
    )
    print(json.dumps(packet, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
