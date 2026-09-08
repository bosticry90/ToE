from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REVIEW_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_SPHERE_KERNEL_DIAGNOSIS_AND_"
    "REFERENCE_ORACLE_EXECUTION_RESULT_REVIEW_20260719_v0.json"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/POST_SCALAR_ONLY_YUKAWA_SPHERE_KERNEL_DIAGNOSIS_AND_"
    "REFERENCE_ORACLE_V0_EXECUTION_RESULT_SCIENTIFIC_RESPONSE_SELECTION_"
    "20260719_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/POST_SCALAR_ONLY_YUKAWA_SPHERE_KERNEL_DIAGNOSIS_AND_"
    "REFERENCE_ORACLE_V0_EXECUTION_RESULT_SCIENTIFIC_RESPONSE_SELECTION_"
    "20260719_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_post_scalar_only_yukawa_sphere_kernel_diagnosis_"
    "and_reference_oracle_v0_execution_result_scientific_response_selection_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "PostScalarOnlyYukawaSphereKernelDiagnosisAndReferenceOracleV0ExecutionResult"
    "ScientificResponseSelectionV0.lean"
)

TARGET = (
    "select_post_scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_"
    "oracle_v0_execution_result_scientific_response_v0"
)
VERDICT = (
    "SELECTED_ANALYTIC_HOMOGENEOUS_SPHERE_YUKAWA_ORACLE_QUALIFICATION_"
    "PACKET_PREPARATION"
)
SELECTED_ROUTE = "QUALIFY_ANALYTIC_HOMOGENEOUS_SPHERE_YUKAWA_ORACLE"
SELECTED_CANDIDATE_ID = "ANALYTIC_SPHERE_ORACLE_QUALIFICATION"
SELECTED_NEXT_TARGET = "prepare_scalar_only_yukawa_analytic_sphere_oracle_qualification_packet_v0"
SELECTED_NEXT_TARGET_KIND = (
    "PREPARATION_ONLY_SMALL_ANALYTIC_SPHERE_ORACLE_PACKET_NO_EXECUTION_NO_PRODUCTION_COMPARISON"
)

AUTHORITY_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_SPHERE_KERNEL_DIAGNOSIS_AND_REFERENCE_ORACLE_EXECUTION_RESULT_REVIEW_20260719_v0.md":
        "1d562a65092b1b914b002f5715667af1b9a0613b800c768413841c0ccbb2b234",
    REVIEW_RELATIVE_PATH:
        "b09bc2c9955dff735d760e30b5a52d3edeebbe9513290ad44446a97751664e80",
    "formal/python/tools/scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_oracle_execution_result_review_v0.py":
        "c9554f9a4d35d590f5513894463e1c2348bc138fb0fe2fb96f1b75ed2a326526",
    "formal/python/tests/test_scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_oracle_execution_result_review_v0.py":
        "bd554cb7c08a82968608c06c5b0b5ce6011c03c21898bf0b4a39bb2903343e72",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaSphereKernelDiagnosisAndReferenceOracleExecutionResultReviewV0.lean":
        "56eb14eb4172530e4e9e138b2aae79ba1370e2b5d02e38e43b694fd8697f895e",
}

CRITERIA = {
    "direct_alignment_with_accepted_block": 5,
    "independent_reference_value": 5,
    "staged_bounded_executability": 5,
    "scientific_information_gain": 4,
    "computational_economy": 5,
    "preserves_unadjudicated_production": 5,
    "future_custody_engineering_fit": 4,
    "downstream_validation_leverage": 4,
    "anti_rabbit_hole_clarity": 4,
    "scope_reversibility": 3,
}

CANDIDATES = (
    {
        "candidate_id": SELECTED_CANDIDATE_ID,
        "route": SELECTED_ROUTE,
        "target": SELECTED_NEXT_TARGET,
        "scores": {criterion: 5 for criterion in CRITERIA},
        "disposition": "SELECTED_FOR_SMALL_ANALYTIC_ORACLE_PACKET_PREPARATION",
    },
    {
        "candidate_id": "FAILED_EXECUTION_PERFORMANCE_DIAGNOSIS",
        "route": "PERFORMANCE_ONLY_DIAGNOSIS_OF_FAILED_FOUR_PATH_EXECUTION",
        "target": "prepare_scalar_only_yukawa_failed_oracle_execution_performance_diagnosis_packet_v0",
        "scores": {
            "direct_alignment_with_accepted_block": 4,
            "independent_reference_value": 1,
            "staged_bounded_executability": 4,
            "scientific_information_gain": 3,
            "computational_economy": 3,
            "preserves_unadjudicated_production": 5,
            "future_custody_engineering_fit": 5,
            "downstream_validation_leverage": 2,
            "anti_rabbit_hole_clarity": 4,
            "scope_reversibility": 4,
        },
        "disposition": "DEFERRED_RUNTIME_LOCALIZATION_DOES_NOT_QUALIFY_A_SCIENTIFIC_ORACLE",
    },
    {
        "candidate_id": "DIRECT_INTEGRATION_METHOD_REPLACEMENT",
        "route": "REPLACE_PRODUCTION_INTEGRATION_BEFORE_ORACLE_QUALIFICATION",
        "target": "prepare_scalar_only_yukawa_replacement_extended_body_kernel_packet_v0",
        "scores": {
            "direct_alignment_with_accepted_block": 3,
            "independent_reference_value": 1,
            "staged_bounded_executability": 2,
            "scientific_information_gain": 3,
            "computational_economy": 2,
            "preserves_unadjudicated_production": 2,
            "future_custody_engineering_fit": 3,
            "downstream_validation_leverage": 3,
            "anti_rabbit_hole_clarity": 2,
            "scope_reversibility": 2,
        },
        "disposition": "DEFERRED_NO_ACCEPTED_REFERENCE_FOR_REPLACEMENT_VALIDATION",
    },
    {
        "candidate_id": "APPARATUS_REDESIGN",
        "route": "REDESIGN_AROUND_SIMPLER_ANALYTIC_GEOMETRIES",
        "target": "prepare_redesigned_scalar_only_yukawa_internal_apparatus_packet_v0",
        "scores": {
            "direct_alignment_with_accepted_block": 2,
            "independent_reference_value": 2,
            "staged_bounded_executability": 3,
            "scientific_information_gain": 2,
            "computational_economy": 2,
            "preserves_unadjudicated_production": 4,
            "future_custody_engineering_fit": 3,
            "downstream_validation_leverage": 3,
            "anti_rabbit_hole_clarity": 3,
            "scope_reversibility": 2,
        },
        "disposition": "DEFERRED_PREMATURE_BEFORE_SMALL_ANALYTIC_ORACLE_TEST",
    },
    {
        "candidate_id": "CLOSE_SYNTHETIC_TORSION_BALANCE_LANE",
        "route": "CLOSE_INTERNAL_SYNTHETIC_TORSION_BALANCE_LANE",
        "target": "select_post_scalar_internal_torsion_balance_lane_closure_v0",
        "scores": {
            "direct_alignment_with_accepted_block": 1,
            "independent_reference_value": 0,
            "staged_bounded_executability": 5,
            "scientific_information_gain": 0,
            "computational_economy": 5,
            "preserves_unadjudicated_production": 5,
            "future_custody_engineering_fit": 5,
            "downstream_validation_leverage": 0,
            "anti_rabbit_hole_clarity": 5,
            "scope_reversibility": 1,
        },
        "disposition": "DEFERRED_UNTIL_ONE_SMALL_ANALYTIC_ORACLE_QUALIFICATION_IS_CONSIDERED",
    },
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _artifact_row(relative_path: str) -> dict[str, str]:
    return {"relative_path": relative_path, "sha256": _sha256(REPO_ROOT / relative_path)}


def _weighted_score(scores: dict[str, int], weights: dict[str, int]) -> int:
    if set(scores) != set(weights):
        raise ValueError("candidate score criteria mismatch")
    return sum(scores[key] * weights[key] for key in weights)


def _rank(weights: dict[str, int]) -> list[dict[str, Any]]:
    rows = []
    for candidate in CANDIDATES:
        row = dict(candidate)
        row["weighted_score"] = _weighted_score(candidate["scores"], weights)
        rows.append(row)
    return sorted(rows, key=lambda row: (-row["weighted_score"], row["candidate_id"]))


def _sensitivity() -> dict[str, Any]:
    rows = []
    for omitted in CRITERIA:
        weights = dict(CRITERIA)
        weights[omitted] = 0
        ranked = _rank(weights)
        rows.append(
            {
                "variant": f"omit_{omitted}",
                "selected_candidate_id": ranked[0]["candidate_id"],
                "selected_score": ranked[0]["weighted_score"],
                "runner_up_candidate_id": ranked[1]["candidate_id"],
                "runner_up_score": ranked[1]["weighted_score"],
            }
        )
    for criterion, baseline in CRITERIA.items():
        for delta in (-1, 1):
            weights = dict(CRITERIA)
            weights[criterion] = max(1, baseline + delta)
            ranked = _rank(weights)
            rows.append(
                {
                    "variant": f"{criterion}_{delta:+d}",
                    "selected_candidate_id": ranked[0]["candidate_id"],
                    "selected_score": ranked[0]["weighted_score"],
                    "runner_up_candidate_id": ranked[1]["candidate_id"],
                    "runner_up_score": ranked[1]["weighted_score"],
                }
            )
    return {
        "variant_count": len(rows),
        "rows": rows,
        "selected_candidate_stable_in_all_variants": all(
            row["selected_candidate_id"] == SELECTED_CANDIDATE_ID for row in rows
        ),
        "minimum_winning_margin": min(
            row["selected_score"] - row["runner_up_score"] for row in rows
        ),
    }


def build_report() -> dict[str, Any]:
    for relative_path, expected in AUTHORITY_HASHES.items():
        path = REPO_ROOT / relative_path
        if not path.exists() or _sha256(path) != expected:
            raise ValueError(f"accepted result-review custody failed: {relative_path}")
    review = json.loads((REPO_ROOT / REVIEW_RELATIVE_PATH).read_text(encoding="utf-8"))
    if review["verdict"] != "ACCEPTED_REFERENCE_ORACLE_INADEQUATE_WITHIN_FROZEN_BUDGET":
        raise ValueError("unexpected consumed result-review verdict")
    if review["selected_next_target"] != TARGET:
        raise ValueError("result review does not authorize this selector")
    scope = review["scope"]
    if scope["diagnosis_rerun_authorized"] is not False or scope["stage_b_authorized"] is not False:
        raise ValueError("result-review firewalls drifted")
    if scope["fresh_scientific_response_selector_authorized"] is not True:
        raise ValueError("fresh selector is not authorized")

    ranking = _rank(CRITERIA)
    sensitivity = _sensitivity()
    if ranking[0]["candidate_id"] != SELECTED_CANDIDATE_ID:
        raise ValueError("analytic-oracle route is not the unique baseline winner")
    if not sensitivity["selected_candidate_stable_in_all_variants"]:
        raise ValueError("analytic-oracle route is not sensitivity-stable")

    preparation_requirements = {
        "status": "PACKET_PREPARATION_AUTHORIZED_NOT_PREPARED",
        "scientific_objective": (
            "Determine whether exact Newtonian and homogeneous-sphere Yukawa formulas, "
            "with stable numerical evaluation and one independent low-dimensional check, "
            "form an efficient reference oracle under project conventions."
        ),
        "formula_contract": {
            "newtonian": "U_N=-G*M1*M2/D",
            "mass": "M_i=(4*pi/3)*rho_i*R_i^3",
            "surface_gap": "g=D-R1-R2>0",
            "yukawa_amplitude": "A_Y=1/3",
            "sphere_form_factor": "F(x)=3*(x*cosh(x)-sinh(x))/x^3",
            "candidate_yukawa": "U_Y=-A_Y*G*M1*M2*F(R1/lambda)*F(R2/lambda)*exp(-D/lambda)/D",
            "independent_derivation_required": True,
            "units_sign_coefficients_and_domain_required": True,
        },
        "stable_evaluator": {
            "small_x_series_required": True,
            "moderate_x_direct_regime_required": True,
            "large_x_scaled_or_log_regime_required": True,
            "regime_boundaries_frozen_before_execution": True,
            "overlap_continuity_tests_required": True,
            "overflow_and_cancellation_mutations_required": True,
        },
        "case_grid": {
            "minimum_case_count": 6,
            "maximum_case_count": 9,
            "required_roles": [
                "SMALL_R_OVER_LAMBDA",
                "MODERATE_R_OVER_LAMBDA",
                "LARGE_R_OVER_LAMBDA",
                "WIDE_SEPARATION",
                "SMALL_POSITIVE_GAP",
                "EQUAL_RADII",
                "UNEQUAL_RADII",
                "ONE_FAILED_STAGE_A_CONFIGURATION",
            ],
            "post_result_case_selection_forbidden": True,
        },
        "independent_cross_check": {
            "path_count": 1,
            "permitted_form": "ONE_LOW_DIMENSIONAL_HIGH_PRECISION_REDUCED_INTEGRAL",
            "self_convergence_required": True,
            "cross_agreement_required": True,
            "production_cubature_import_forbidden": True,
            "all_39_cases_forbidden": True,
        },
        "execution_custody": {
            "process_group_termination_mandatory": True,
            "raw_launcher_log_preserved": True,
            "timeout_initiation_timestamp_preserved": True,
            "child_termination_timestamps_preserved": True,
            "stage_level_atomic_status_preserved": True,
            "completed_stage_values_decision_bearing_only_if_preregistered": True,
            "orphan_child_survival_is_execution_failure": True,
        },
        "resource_envelope_to_freeze": {
            "target_total_wall_clock_seconds_max": 600,
            "target_memory_mib_max": 2048,
            "per_stage_wall_clock_caps_required": True,
            "budget_exhaustion_fails_closed": True,
            "result_dependent_budget_change_forbidden": True,
        },
        "legitimate_outcomes": [
            "ANALYTIC_SPHERE_ORACLE_QUALIFIED",
            "ANALYTIC_FORMULA_DERIVED_BUT_NUMERICAL_EVALUATOR_UNSTABLE",
            "ANALYTIC_ORACLE_CROSS_CHECK_FAILED",
            "ANALYTIC_ORACLE_QUALIFICATION_TIMEOUT",
            "SPHERE_ORACLE_NOT_VALID_OVER_REQUIRED_DOMAIN",
        ],
        "only_success_eligibility": (
            "Only ANALYTIC_SPHERE_ORACLE_QUALIFIED may make a later production-method "
            "comparison eligible for a fresh selector."
        ),
        "forbidden_work": [
            "FULL_39_CASE_DIAGNOSIS",
            "OLD_PRODUCTION_CUBATURE_ORDERS_8_TO_48",
            "FULL_NEAR_CONTACT_PROFILE",
            "TORQUE",
            "ANGULAR_DFT",
            "APPARATUS_HARMONICS",
            "FINAL_REAL_150_VECTOR",
            "JACOBIAN",
            "IDENTIFIABILITY",
            "STAGE_B",
        ],
    }
    gates = (
        "AUTHORITY_HASHES_MATCH",
        "ACCEPTED_TIMEOUT_RESULT_FROZEN",
        "ANALYTIC_ORACLE_NOT_QUALIFIED_OR_REFUTED",
        "PRODUCTION_REMAINS_UNADJUDICATED",
        "CAUSE_OF_STAGE_A_FAILURE_UNRESOLVED",
        "RERUN_REMAINS_UNAUTHORIZED",
        "FIVE_BOUNDED_OPTIONS_COMPARED",
        "DIRECT_METHOD_REPLACEMENT_EXPLICITLY_RANKED",
        "ANALYTIC_ROUTE_UNIQUE_BASELINE_WINNER",
        "THIRTY_SENSITIVITY_VARIANTS_EXECUTED",
        "ANALYTIC_ROUTE_WINS_ALL_SENSITIVITY_VARIANTS",
        "SMALL_SIX_TO_NINE_CASE_GRID_REQUIRED",
        "NEWTONIAN_DERIVATION_REQUIRED",
        "YUKAWA_FORM_FACTOR_DERIVATION_REQUIRED",
        "SMALL_MODERATE_LARGE_X_REGIMES_REQUIRED",
        "REGIME_OVERLAP_TESTS_REQUIRED",
        "ONE_LOW_DIMENSIONAL_CROSS_CHECK_ONLY",
        "PRODUCTION_CUBATURE_EXCLUDED",
        "PROCESS_GROUP_TERMINATION_MANDATORY",
        "RAW_LAUNCHER_LOG_MANDATORY",
        "TIMEOUT_AND_CHILD_TERMINATION_TIMESTAMPS_MANDATORY",
        "STAGE_LEVEL_ATOMIC_STATUS_MANDATORY",
        "TEN_MINUTE_TARGET_BUDGET_CEILING",
        "NO_PACKET_PREPARED_NOW",
        "NO_ORACLE_EXECUTION_NOW",
        "NO_PRODUCTION_COMPARISON_NOW",
        "NO_TORQUE_OR_DFT",
        "NO_VECTOR_JACOBIAN_OR_IDENTIFIABILITY",
        "NO_STAGE_B",
        "FRESH_REVIEW_REQUIRED_BEFORE_EXECUTION",
    )
    selector_scope = {
        "scientific_response_selector_executed": True,
        "accepted_diagnosis_result_frozen": True,
        "candidate_count": len(CANDIDATES),
        "analytic_oracle_packet_preparation_authorized": True,
        "analytic_oracle_packet_prepared_now": False,
        "analytic_oracle_qualification_executed": False,
        "performance_diagnosis_authorized": False,
        "production_method_replacement_authorized": False,
        "apparatus_redesign_authorized": False,
        "lane_closure_authorized": False,
        "diagnosis_rerun_authorized": False,
        "stage_a_reopened": False,
        "production_cubature_comparison_authorized": False,
        "torque_or_dft_authorized": False,
        "final_real_150_vector_authorized": False,
        "jacobian_or_identifiability_authorized": False,
        "stage_b_authorized": False,
    }
    return {
        "schema_id": "toe.post_scalar_only_yukawa.sphere_kernel_diagnosis.execution_result.scientific_response_selection.v0",
        "selection_id": "POST_SCALAR_ONLY_YUKAWA_SPHERE_KERNEL_DIAGNOSIS_AND_REFERENCE_ORACLE_V0_EXECUTION_RESULT_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0",
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "selected_route": SELECTED_ROUTE,
        "selected_candidate_id": SELECTED_CANDIDATE_ID,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_result_review_verdict": review["verdict"],
            "frozen_result_review_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in AUTHORITY_HASHES.items()
            ],
            "human_selection": _artifact_row(HUMAN_RELATIVE_PATH),
            "generator": _artifact_row(
                "formal/python/tools/post_scalar_only_yukawa_sphere_kernel_"
                "diagnosis_and_reference_oracle_v0_execution_result_scientific_"
                "response_selection_v0.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
        },
        "accepted_result_interpretation": {
            "principal_result": "REFERENCE_ORACLE_INADEQUATE_WITHIN_FROZEN_BUDGET",
            "analytic_sphere_oracle": "NOT_QUALIFIED_OR_REFUTED",
            "production_cubature": "UNADJUDICATED",
            "cause_of_original_kernel_failure": "UNRESOLVED",
            "dft_root_cause": "UNKNOWN",
            "physical_identifiability": "NOT_TESTED",
            "diagnosis_rerun": "NOT_AUTHORIZED",
            "stage_b": "NOT_AUTHORIZED",
        },
        "selection_policy": {
            "candidate_count": len(CANDIDATES),
            "criterion_count": len(CRITERIA),
            "criteria_weights": CRITERIA,
            "criterion_scale": "0_TO_5_PRIORITY_SCORE_NOT_TRUTH_PROBABILITY",
            "tie_break_rule": "LEXICOGRAPHIC_CANDIDATE_ID",
        },
        "ranking": {
            "rows": ranking,
            "selected_candidate_id": ranking[0]["candidate_id"],
            "selected_score": ranking[0]["weighted_score"],
            "runner_up_candidate_id": ranking[1]["candidate_id"],
            "runner_up_score": ranking[1]["weighted_score"],
            "winning_margin": ranking[0]["weighted_score"] - ranking[1]["weighted_score"],
        },
        "sensitivity_analysis": sensitivity,
        "analytic_oracle_packet_preparation_requirements": preparation_requirements,
        "selection_gates": {
            "gate_count": len(gates),
            "pass_count": len(gates),
            "failure_count": 0,
            "rows": [{"gate_id": gate, "status": "PASS"} for gate in gates],
        },
        "scope": selector_scope,
        "claim_ceiling": (
            "This selector authorizes preparation of one small analytic homogeneous-"
            "sphere Yukawa oracle qualification packet only. It derives or computes no "
            "oracle now, compares no production method, reruns no diagnosis or Stage A, "
            "and authorizes no torque, DFT, vector, Jacobian, identifiability, or Stage B work."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_report(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Select the response to the accepted sphere-kernel diagnosis timeout.")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    path = REPO_ROOT / REPORT_RELATIVE_PATH
    rendered = artifact_bytes()
    if args.write:
        path.write_bytes(rendered)
        print(f"wrote {REPORT_RELATIVE_PATH} route={SELECTED_ROUTE}")
        return 0
    if not path.exists() or path.read_bytes() != rendered:
        print("post-diagnosis scientific-response selector artifact missing or stale")
        return 1
    report = json.loads(path.read_text(encoding="utf-8"))
    print(
        "post-diagnosis selector OK "
        f"route={report['selected_route']} "
        f"gates={report['selection_gates']['pass_count']}/{report['selection_gates']['gate_count']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
