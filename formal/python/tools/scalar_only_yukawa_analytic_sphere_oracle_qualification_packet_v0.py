from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_"
    "QUALIFICATION_PACKET_20260719_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_"
    "QUALIFICATION_PACKET_20260719_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_scalar_only_yukawa_analytic_sphere_oracle_"
    "qualification_packet_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ScalarOnlyYukawaAnalyticSphereOracleQualificationPacketV0.lean"
)
SELECTOR_RELATIVE_PATH = (
    "formal/docs/release/POST_SCALAR_ONLY_YUKAWA_SPHERE_KERNEL_DIAGNOSIS_AND_"
    "REFERENCE_ORACLE_V0_EXECUTION_RESULT_SCIENTIFIC_RESPONSE_SELECTION_"
    "20260719_v0.json"
)

TARGET = "prepare_scalar_only_yukawa_analytic_sphere_oracle_qualification_packet_v0"
VERDICT = "PREPARED_SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_QUALIFICATION_PACKET_V0"
SELECTED_NEXT_TARGET = (
    "review_scalar_only_yukawa_analytic_sphere_oracle_qualification_packet_v0_result"
)
SELECTED_NEXT_TARGET_KIND = (
    "INDEPENDENT_PACKET_REVIEW_ONLY_NO_ORACLE_QUALIFICATION_EXECUTION"
)

SELECTOR_HASHES = {
    "formal/docs/lanes/POST_SCALAR_ONLY_YUKAWA_SPHERE_KERNEL_DIAGNOSIS_AND_REFERENCE_ORACLE_V0_EXECUTION_RESULT_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0.md":
        "ae3d4a16fbe4859dfb432c9533ab16dc3bad90271e027330ae8a4edf2f5241f2",
    SELECTOR_RELATIVE_PATH:
        "b6e04f13348a103a83c99ea0bbc8261e36d32e1f8540042c5aa84e40b056b265",
    "formal/python/tools/post_scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_oracle_v0_execution_result_scientific_response_selection_v0.py":
        "96229baacd0a05b97b7caaddfee85158fde939e561feb0e8c4363676e6309bda",
    "formal/python/tests/test_post_scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_oracle_v0_execution_result_scientific_response_selection_v0.py":
        "d7ac6251f86ed96ebb97e87230667e721a4046f0e20e334180507a95d0cd8520",
    "formal/toe_formal/ToeFormal/Derivation/PostScalarOnlyYukawaSphereKernelDiagnosisAndReferenceOracleV0ExecutionResultScientificResponseSelectionV0.lean":
        "f58b52e14d34979e07f2926f337d02a8ee46df2dab1fc3e3debff94f727e5d5b",
}

CASES = (
    ("LEGACY_STAGE_A_00_LARGE_X", 5e-3, 5e-3, 1e-3, 1e-4,
     ("FAILED_STAGE_A_CONFIGURATION", "EQUAL_RADII", "LARGE_X")),
    ("LEGACY_STAGE_A_01_TRANSITION", 5e-3, 5e-3, 2e-2, 5e-3,
     ("FAILED_STAGE_A_CONFIGURATION", "EQUAL_RADII", "X_NEAR_ONE", "WIDE_SEPARATION")),
    ("LEGACY_STAGE_A_02_LONG_RANGE", 5e-3, 5e-3, 7e-2, 1e-1,
     ("FAILED_STAGE_A_CONFIGURATION", "EQUAL_RADII", "SMALL_X", "WIDE_SEPARATION")),
    ("SMALL_X_UNEQUAL_WIDE", 1e-3, 3e-3, 2e-2, 1.0,
     ("UNEQUAL_RADII", "SMALL_X", "POINT_PARTICLE_LIMIT", "WIDE_SEPARATION")),
    ("MIXED_X_UNEQUAL", 2e-3, 8e-3, 2e-3, 4e-3,
     ("UNEQUAL_RADII", "MIXED_X", "TRANSITION_DOMAIN")),
    ("SMALL_GAP_LARGE_X", 5e-3, 5e-3, 1e-5, 1e-5,
     ("EQUAL_RADII", "SMALL_POSITIVE_GAP", "LARGE_X")),
    ("EXTREME_X_1000_UNEQUAL", 5e-3, 2.5e-3, 5e-6, 5e-6,
     ("UNEQUAL_RADII", "SMALL_POSITIVE_GAP", "X_MAX_1000")),
    ("LONG_RANGE_UNEQUAL_WIDE", 2e-3, 8e-3, 5e-2, 5e-1,
     ("UNEQUAL_RADII", "SMALL_X", "LONG_RANGE", "WIDE_SEPARATION")),
)

TERMINAL_OUTCOMES = (
    "ANALYTIC_SPHERE_ORACLE_QUALIFIED",
    "ANALYTIC_FORMULA_DERIVED_BUT_NUMERICAL_EVALUATOR_UNSTABLE",
    "ANALYTIC_ORACLE_CROSS_CHECK_FAILED",
    "ANALYTIC_ORACLE_QUALIFICATION_TIMEOUT",
    "SPHERE_ORACLE_NOT_VALID_OVER_REQUIRED_DOMAIN",
)

PACKET_REVIEW_OUTCOMES = (
    "ANALYTIC_SPHERE_ORACLE_QUALIFICATION_CONTRACT_READY",
    "BLOCKED_ANALYTIC_DERIVATION_CONTRACT",
    "BLOCKED_STABLE_EVALUATOR_CONTRACT",
    "BLOCKED_REPRESENTATIVE_CASE_GRID",
    "BLOCKED_INDEPENDENT_CROSS_CHECK_CONTRACT",
    "BLOCKED_RESOURCE_AND_PROCESS_CUSTODY",
    "BLOCKED_MUTATION_ROUTING",
    "BLOCKED_SCOPE_OR_PROVENANCE",
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _artifact_row(relative_path: str) -> dict[str, str]:
    return {"relative_path": relative_path, "sha256": _sha256(REPO_ROOT / relative_path)}


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _case_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for case_id, r1, r2, gap, lambda_m, roles in CASES:
        center_distance = r1 + r2 + gap
        rows.append({
            "case_id": case_id,
            "radius_1_m": r1,
            "radius_2_m": r2,
            "density_1_kg_m3": 19250.0,
            "density_2_kg_m3": 19250.0,
            "surface_gap_m": gap,
            "center_distance_m": center_distance,
            "lambda_m": lambda_m,
            "x_1": round(r1 / lambda_m, 12),
            "x_2": round(r2 / lambda_m, 12),
            "g_over_lambda": round(gap / lambda_m, 12),
            "strictly_nonoverlapping": center_distance > r1 + r2 and gap > 0.0,
            "roles": list(roles),
        })
    return rows


def build_report() -> dict[str, Any]:
    for relative_path, expected in SELECTOR_HASHES.items():
        path = REPO_ROOT / relative_path
        if not path.exists() or _sha256(path) != expected:
            raise ValueError(f"selector authority drift: {relative_path}")
    selector = _load_json(SELECTOR_RELATIVE_PATH)
    if selector.get("selected_next_target") != TARGET:
        raise ValueError("selector did not authorize this packet preparation")
    if selector.get("selected_route") != "QUALIFY_ANALYTIC_HOMOGENEOUS_SPHERE_YUKAWA_ORACLE":
        raise ValueError("selector route mismatch")
    if selector.get("scope", {}).get("analytic_oracle_qualification_executed") is not False:
        raise ValueError("selector unexpectedly executed oracle qualification")

    cases = _case_rows()
    if not 6 <= len(cases) <= 9 or not all(row["strictly_nonoverlapping"] for row in cases):
        raise ValueError("representative case grid is outside its bounded non-overlap contract")
    if max(max(row["x_1"], row["x_2"]) for row in cases) != 1000.0:
        raise ValueError("case grid does not bind the required x=1000 endpoint")

    preparation_gates = (
        "EXACT_SELECTOR_AUTHORITY_AND_TARGET",
        "ACCEPTED_REFERENCE_TIMEOUT_RESULT_FROZEN",
        "PACKET_PREPARATION_ONLY_NO_EXECUTION",
        "NEWTONIAN_SHELL_THEOREM_FORMULA_FROZEN",
        "CENTER_DISTANCE_SURFACE_GAP_MASS_UNITS_AND_SIGN_FROZEN",
        "STRICT_NONOVERLAP_REQUIRED_FOR_EVERY_CASE",
        "YUKAWA_FORM_FACTOR_DERIVATION_OBLIGATIONS_FROZEN",
        "YUKAWA_A_Y_ONE_THIRD_AND_CENTER_EXPONENTIAL_FROZEN",
        "POINT_PARTICLE_LIMIT_AND_SPHERE_EXCHANGE_SYMMETRY_FROZEN",
        "SMALL_X_SERIES_THROUGH_X_EIGHT_FROZEN",
        "SMALL_X_TRUNCATION_AND_PRIMARY_BOUNDARY_FROZEN",
        "MODERATE_X_DIRECT_REGIME_FROZEN",
        "LARGE_X_SCALED_FACTOR_REGIME_FROZEN",
        "SURFACE_GAP_SCALED_PAIR_IDENTITY_FROZEN",
        "LOG_DOMAIN_UNDERFLOW_RECORDING_FROZEN",
        "TWO_REGIME_OVERLAP_GRIDS_AND_TOLERANCES_FROZEN",
        "EIGHT_CASE_GRID_EXACT_AND_POST_RESULT_SELECTION_FORBIDDEN",
        "SMALL_TRANSITION_LARGE_EQUAL_UNEQUAL_WIDE_AND_SMALL_GAP_ROLES_COVERED",
        "ALL_THREE_FAILED_STAGE_A_CONFIGURATIONS_INCLUDED",
        "REQUIRED_X_1000_ENDPOINT_INCLUDED",
        "ONE_SCALED_RADIAL_CROSS_CHECK_ONLY",
        "CROSS_CHECK_DOES_NOT_CALL_ANALYTIC_FORM_FACTOR",
        "PRODUCTION_CUBATURE_IMPORT_AND_39_CASE_GRID_FORBIDDEN",
        "CROSS_CHECK_PRECISION_LADDER_AND_SELF_CONVERGENCE_FROZEN",
        "EVALUATOR_AND_ENERGY_AGREEMENT_TOLERANCES_FROZEN",
        "PER_STAGE_TIMEOUTS_AND_TOTAL_BUDGET_FROZEN",
        "MEMORY_LIMIT_AND_FAIL_CLOSED_BUDGET_RULE_FROZEN",
        "PROCESS_GROUP_TERMINATION_MANDATORY",
        "RAW_LAUNCHER_TRANSCRIPT_PRESERVED",
        "TIMEOUT_AND_CHILD_TERMINATION_TIMESTAMPS_PRESERVED",
        "STAGE_LEVEL_ATOMIC_OUTPUTS_FROZEN",
        "EIGHT_LIVE_EVALUATOR_MUTATIONS_FROZEN",
        "FIVE_TERMINAL_OUTCOMES_EXACT",
        "ONLY_QUALIFIED_OUTCOME_MAY_ENABLE_FRESH_PRODUCTION_COMPARISON_SELECTION",
        "INDEPENDENT_PACKET_REVIEW_OUTCOMES_FROZEN",
        "NO_ORACLE_VALUE_COMPUTED_DURING_PREPARATION",
        "NO_PRODUCTION_COMPARISON_OR_METHOD_REPLACEMENT",
        "NO_TORQUE_DFT_OR_APPARATUS_HARMONICS",
        "NO_VECTOR_JACOBIAN_SVD_OR_IDENTIFIABILITY",
        "NO_STAGE_A_RERUN_V2_OR_STAGE_B",
        "ONE_EXECUTION_ONLY_AFTER_ACCEPTED_INDEPENDENT_REVIEW",
        "FRESH_RESULT_REVIEW_AND_SELECTOR_REQUIRED_AFTER_FUTURE_EXECUTION",
    )

    scope = {
        "analytic_oracle_packet_prepared": True,
        "selector_authority_consumed": True,
        "case_grid_constructed_as_contract_metadata": True,
        "independent_packet_review_required": True,
        "oracle_qualification_execution_authorized": False,
        "oracle_qualification_executed": False,
        "newtonian_energy_computed": False,
        "yukawa_energy_computed": False,
        "analytic_form_factor_evaluated": False,
        "independent_radial_integral_evaluated": False,
        "mutation_executed": False,
        "oracle_qualification_status_issued": False,
        "production_cubature_imported": False,
        "production_cubature_compared": False,
        "production_integration_method_changed": False,
        "diagnosis_rerun_authorized": False,
        "stage_a_rerun_authorized": False,
        "automatic_v2_authorized": False,
        "torque_authorized": False,
        "angular_dft_authorized": False,
        "apparatus_harmonics_authorized": False,
        "final_real_150_vector_authorized": False,
        "jacobian_authorized": False,
        "svd_authorized": False,
        "identifiability_authorized": False,
        "stage_b_eligible": False,
        "stage_b_authorized": False,
    }

    return {
        "schema_id": "toe.scalar_only_yukawa.analytic_sphere_oracle.qualification_packet.v0",
        "packet_id": "SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_QUALIFICATION_PACKET_20260719_v0",
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "status": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_selector_verdict": selector["verdict"],
            "consumed_selector_route": selector["selected_route"],
            "frozen_selector_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in SELECTOR_HASHES.items()
            ],
            "human_packet": _artifact_row(HUMAN_RELATIVE_PATH),
            "generator": _artifact_row(
                "formal/python/tools/scalar_only_yukawa_analytic_sphere_oracle_"
                "qualification_packet_v0.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
        },
        "accepted_state_anchor": {
            "stage_a_result": "BLOCKED_PRODUCTION_KERNEL_VALIDATION",
            "broad_diagnosis_result": "REFERENCE_ORACLE_INADEQUATE_WITHIN_FROZEN_BUDGET",
            "analytic_sphere_oracle": "NOT_QUALIFIED_OR_REFUTED",
            "production_cubature": "UNADJUDICATED",
            "original_kernel_failure_cause": "UNRESOLVED",
            "diagnosis_rerun": "NOT_AUTHORIZED",
            "stage_b": "NOT_AUTHORIZED",
        },
        "physical_conventions": {
            "gravitational_constant_m3_kg_s2": 6.67430e-11,
            "yukawa_amplitude_exact": "1/3",
            "default_density_kg_m3": 19250.0,
            "mass_formula": "M_i=(4*pi/3)*rho_i*R_i^3",
            "center_distance_symbol": "D",
            "surface_gap_definition": "g=D-R1-R2",
            "strict_nonoverlap_rule": "D>R1+R2 equivalently g>0",
            "positive_radius_density_and_lambda_required": True,
            "energy_unit": "J",
            "newtonian_sign": "NEGATIVE_ATTRACTIVE",
            "yukawa_sign_for_POSITIVE_A_Y": "NEGATIVE_ATTRACTIVE",
        },
        "derivation_contract": {
            "newtonian_oracle": "U_N(D)=-G*M1*M2/D",
            "dimensionless_radius": "x_i=R_i/lambda",
            "sphere_form_factor": "F(x)=3*(x*cosh(x)-sinh(x))/x^3",
            "yukawa_oracle": "U_Y(D)=-(1/3)*G*M1*M2*F(x1)*F(x2)*exp(-D/lambda)/D",
            "domain": "STRICTLY_NONOVERLAPPING_HOMOGENEOUS_SPHERES",
            "obligations": [
                "DERIVE_NEWTONIAN_EXTERNAL_SPHERE_FIELD_AND_PAIR_ENERGY",
                "DERIVE_YUKAWA_EXTERNAL_HOMOGENEOUS_SPHERE_FIELD_BY_RADIAL_INTEGRATION",
                "DERIVE_TWO_SPHERE_NONOVERLAP_PAIR_COMPOSITION",
                "VERIFY_PROJECT_NORMALIZATION_A_Y_EQUALS_ONE_THIRD",
                "VERIFY_BOTH_FORM_FACTORS_AND_CENTER_DISTANCE_EXPONENTIAL",
                "VERIFY_POINT_PARTICLE_LIMIT_F_TO_ONE",
                "VERIFY_SPHERE_EXCHANGE_SYMMETRY_UNITS_AND_SIGN",
                "DERIVE_SCALED_FACTOR_AND_SURFACE_GAP_PAIR_IDENTITY",
            ],
            "derivation_may_be_replaced_by_standard_formula_citation": False,
        },
        "stable_evaluator_contract": {
            "common_scaled_output": "H(x)=exp(-x)*F(x)",
            "small_x": {
                "primary_domain": "0<x<=0.1",
                "formula": "F_series=1+x^2/10+x^4/280+x^6/15120+x^8/1330560",
                "scaled_output": "H=exp(-x)*F_series",
                "fixed_highest_power": 8,
                "truncation_check": "120_DIGIT_DIRECT_OR_RADIAL_REFERENCE_IN_OVERLAP",
            },
            "moderate_x": {
                "primary_domain": "0.1<x<=40",
                "formula": "H=exp(-x)*3*(x*cosh(x)-sinh(x))/x^3",
                "binary64_finite_required": True,
            },
            "large_x": {
                "primary_domain": "40<x<=1000",
                "formula": "H=3*((x-1)+(x+1)*exp(-2*x))/(2*x^3)",
                "direct_sinh_or_cosh_forbidden": True,
            },
            "stable_pair_factor": "exp(-D/lambda)*F(x1)*F(x2)=exp(-g/lambda)*H(x1)*H(x2)",
            "stable_yukawa_energy": "U_Y=-(1/3)*G*M1*M2*exp(-g/lambda)*H(x1)*H(x2)/D",
            "log_domain_energy_required": True,
            "silent_overflow_or_underflow_forbidden": True,
            "binary64_underflow_rule": (
                "PRESERVE_HIGH_PRECISION_VALUE_AND_LOG10_ABS_ENERGY_AND_LABEL_"
                "BINARY64_UNDERFLOW_IF_LOG_ABS_BELOW_LOG_MIN_SUBNORMAL"
            ),
            "overlap_checks": [
                {
                    "overlap_id": "SMALL_DIRECT",
                    "x_values": [0.05, 0.1, 0.2],
                    "absolute_tolerance_H": 5e-14,
                    "relative_tolerance_H": 5e-11,
                },
                {
                    "overlap_id": "DIRECT_SCALED",
                    "x_values": [20.0, 32.0, 40.0],
                    "absolute_tolerance_H": 5e-15,
                    "relative_tolerance_H": 5e-13,
                },
            ],
            "post_result_regime_boundary_change": "FORBIDDEN",
        },
        "representative_domain": {
            "case_count": len(cases),
            "minimum_case_count": 6,
            "maximum_case_count": 9,
            "maximum_x": max(max(row["x_1"], row["x_2"]) for row in cases),
            "failed_stage_a_case_count": sum(
                "FAILED_STAGE_A_CONFIGURATION" in row["roles"] for row in cases
            ),
            "rows": cases,
            "post_result_case_addition_removal_or_shift": "FORBIDDEN",
        },
        "independent_cross_check_contract": {
            "path_count": 1,
            "path_id": "R1_SCALED_HIGH_PRECISION_RADIAL_MOMENT_INTEGRAL",
            "dimension": 1,
            "scaled_integral": (
                "H_radial(x)=3/(2*x)*integral_0^1 u*exp(-x*(1-u))*"
                "(-expm1(-2*x*u)) du"
            ),
            "derivation_identity": "H_radial(x)=exp(-x)*3/x^3*integral_0^x t*sinh(t)dt",
            "quadrature": "ARBITRARY_PRECISION_TANH_SINH",
            "decimal_precision_ladder": [50, 80, 120],
            "plateau_levels": [80, 120],
            "all_eight_cases": True,
            "analytic_form_factor_call_forbidden": True,
            "closed_form_scaled_factor_call_forbidden": True,
            "production_kernel_or_cubature_import_forbidden": True,
            "self_convergence": {
                "absolute_tolerance_H": 1e-30,
                "relative_tolerance_H": 1e-24,
                "rule": "abs(H_120-H_80)<=1e-30+1e-24*abs(H_120)",
            },
            "cross_agreement": {
                "stable_evaluator_absolute_tolerance_H": 5e-15,
                "stable_evaluator_relative_tolerance_H": 5e-12,
                "energy_absolute_tolerance_J": 1e-38,
                "energy_relative_tolerance": 5e-12,
                "rule": "absolute AND relative envelope uses abs(delta)<=abs_tol+rel_tol*abs(reference)",
            },
            "failed_plateau_outcome": "ANALYTIC_ORACLE_CROSS_CHECK_FAILED",
            "timeout_outcome": "ANALYTIC_ORACLE_QUALIFICATION_TIMEOUT",
        },
        "resource_and_custody_contract": {
            "total_wall_clock_seconds_max": 600,
            "memory_mib_max": 2048,
            "stage_rows": [
                {"stage_id": "O1_PREFLIGHT_AND_CUSTODY", "wall_clock_seconds_max": 20},
                {"stage_id": "O2_DERIVATION_DOMAIN_AND_DIMENSIONS", "wall_clock_seconds_max": 60},
                {"stage_id": "O3_STABLE_EVALUATOR_AND_OVERLAPS", "wall_clock_seconds_max": 90},
                {"stage_id": "O4_INDEPENDENT_RADIAL_CROSS_CHECK", "wall_clock_seconds_max": 300},
                {"stage_id": "O5_MUTATIONS_AND_ADJUDICATION", "wall_clock_seconds_max": 90},
                {"stage_id": "O6_ATOMIC_FINALIZATION", "wall_clock_seconds_max": 40},
            ],
            "process_group_termination": "MANDATORY",
            "raw_launcher_transcript": "PRESERVED",
            "timeout_initiation_timestamp": "PRESERVED",
            "child_process_tree_and_termination_timestamps": "PRESERVED",
            "zero_surviving_process_check": "MANDATORY",
            "stage_level_atomic_status": "REQUIRED",
            "stage_status_values": ["NOT_STARTED", "COMPLETE", "FAILED", "TIMEOUT"],
            "completed_stage_values_decision_bearing_only_if_preregistered": True,
            "packet_wide_qualified_outcome_requires_all_stages_complete": True,
            "budget_or_custody_failure": "FAIL_CLOSED",
            "result_dependent_budget_change": "FORBIDDEN",
        },
        "mutation_controls": {
            "mutation_count": 8,
            "same_live_oracle_evaluator_and_adjudicator_required": True,
            "metadata_only_rejection_forbidden": True,
            "rows": [
                {"mutation_id": "INTERPRET_RADIUS_AS_DIAMETER", "required_result": "FAIL"},
                {"mutation_id": "USE_SURFACE_GAP_AS_CENTER_DISTANCE", "required_result": "FAIL"},
                {"mutation_id": "OMIT_FOUR_PI_OVER_THREE_MASS_FACTOR", "required_result": "FAIL"},
                {"mutation_id": "OMIT_A_Y_ONE_THIRD", "required_result": "FAIL"},
                {"mutation_id": "OMIT_SECOND_SPHERE_FORM_FACTOR", "required_result": "FAIL"},
                {"mutation_id": "FLIP_YUKAWA_EXPONENTIAL_SIGN", "required_result": "FAIL"},
                {"mutation_id": "FORCE_DIRECT_LARGE_X_SINH_COSH_PATH", "required_result": "FAIL"},
                {"mutation_id": "FORCE_DIRECT_SMALL_X_CANCELLATION_PATH", "required_result": "FAIL"},
            ],
        },
        "execution_output_contract": {
            "authorized_only_after_accepted_review": [
                "DERIVATION_OBLIGATION_STATUS",
                "NEWTONIAN_ORACLE_VALUES",
                "STABLE_YUKAWA_ORACLE_VALUES",
                "REGIME_OVERLAP_RESULTS",
                "INDEPENDENT_RADIAL_CROSS_CHECK_VALUES",
                "ABSOLUTE_AND_RELATIVE_ERRORS",
                "PRECISION_RUNTIME_AND_CUSTODY_RECORDS",
                "MUTATION_RESULTS",
                "ONE_TERMINAL_ORACLE_QUALIFICATION_STATUS",
            ],
            "terminal_outcomes": list(TERMINAL_OUTCOMES),
            "only_success_eligibility": (
                "Only ANALYTIC_SPHERE_ORACLE_QUALIFIED may make a later production-method "
                "comparison eligible for a fresh scientific-response selector."
            ),
            "forbidden_outputs": [
                "PRODUCTION_CUBATURE_JUDGMENT",
                "PRODUCTION_INTEGRATION_REPLACEMENT",
                "TORQUE",
                "ANGULAR_DFT",
                "APPARATUS_HARMONICS",
                "FINAL_REAL_150_VECTOR",
                "JACOBIAN_OR_SVD",
                "IDENTIFIABILITY",
                "SENSITIVITY_FORECAST_OR_STAGE_B",
            ],
        },
        "packet_review_contract": {
            "independent_review_required": True,
            "review_outcomes": list(PACKET_REVIEW_OUTCOMES),
            "ready_outcome_authorizes": "ONE_SMALL_ANALYTIC_ORACLE_QUALIFICATION_EXECUTION_ONLY",
            "authorized_execution_count": 1,
            "executions_consumed": 0,
            "ready_outcome_does_not_authorize": [
                "PRODUCTION_CUBATURE_COMPARISON",
                "INTEGRATION_METHOD_REPLACEMENT",
                "STAGE_A_RERUN_OR_V2",
                "TORQUE_OR_DFT",
                "IDENTIFIABILITY",
                "STAGE_B",
            ],
            "post_execution_independent_result_review_required": True,
            "post_result_fresh_scientific_response_selector_required": True,
        },
        "preparation_gates": {
            "gate_count": len(preparation_gates),
            "pass_count": len(preparation_gates),
            "failure_count": 0,
            "rows": [{"gate_id": gate, "status": "PASS"} for gate in preparation_gates],
        },
        "scope": scope,
        "claim_ceiling": (
            "This packet preregisters one small analytic homogeneous-sphere oracle "
            "qualification contract. It computes no interaction value, executes no "
            "oracle or mutation, judges or replaces no production method, and authorizes "
            "no execution until independent packet review."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_report(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Prepare the analytic homogeneous-sphere oracle qualification packet without executing it."
    )
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    rendered = artifact_bytes()
    if args.write:
        report_path.write_bytes(rendered)
        print(f"wrote {REPORT_RELATIVE_PATH} status=PREPARED_PENDING_INDEPENDENT_REVIEW")
        return 0
    if not report_path.exists() or report_path.read_bytes() != rendered:
        print("analytic sphere oracle qualification packet artifact missing or stale")
        return 1
    report = json.loads(report_path.read_text(encoding="utf-8"))
    print(
        "analytic sphere oracle qualification packet OK "
        f"gates={report['preparation_gates']['pass_count']}/"
        f"{report['preparation_gates']['gate_count']} execution=0/1"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
