from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_SPHERE_KERNEL_DIAGNOSIS_AND_"
    "REFERENCE_ORACLE_PACKET_20260719_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_SPHERE_KERNEL_DIAGNOSIS_AND_"
    "REFERENCE_ORACLE_PACKET_20260719_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_scalar_only_yukawa_sphere_kernel_diagnosis_and_"
    "reference_oracle_packet_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ScalarOnlyYukawaSphereKernelDiagnosisAndReferenceOraclePacketV0.lean"
)
SELECTOR_RELATIVE_PATH = (
    "formal/docs/release/POST_SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_"
    "FORWARD_MODEL_VALIDATION_V1_EXECUTION_RESULT_SCIENTIFIC_RESPONSE_"
    "SELECTION_20260719_v0.json"
)

TARGET = (
    "prepare_scalar_only_yukawa_sphere_kernel_diagnosis_and_"
    "reference_oracle_packet_v0"
)
VERDICT = "PREPARED_BOUNDED_SPHERE_KERNEL_DIAGNOSIS_AND_REFERENCE_ORACLE_PACKET_V0"
SELECTED_NEXT_TARGET = (
    "review_scalar_only_yukawa_sphere_kernel_diagnosis_and_"
    "reference_oracle_packet_v0_result"
)
SELECTED_NEXT_TARGET_KIND = (
    "INDEPENDENT_PACKET_REVIEW_ONLY_NO_DIAGNOSIS_EXECUTION"
)

SELECTOR_HASHES = {
    "formal/docs/lanes/POST_SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_FORWARD_MODEL_VALIDATION_V1_EXECUTION_RESULT_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0.md":
        "948a0712ae8693dad2c8d0b3041397eca0255b85f9fb4c9e2b577cf5cfe3c2b0",
    SELECTOR_RELATIVE_PATH:
        "311685e057d5f1e9f99218775ea841d33198ef85de2f7a41bdc85f20e85b5cd8",
    "formal/python/tools/post_scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_v1_execution_result_scientific_response_selection_v0.py":
        "6ff38f90ec5a92f1919fb75c62fcd4680c31a5b897d2debabf610b33e1134324",
    "formal/python/tests/test_post_scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_v1_execution_result_scientific_response_selection_v0.py":
        "d745ee1e5705c2206b3b178cf512ae99dd11d38a61a04c0eed5deadeac6af380",
    "formal/toe_formal/ToeFormal/Derivation/PostScalarOnlyYukawaDeterministicTorsionBalanceForwardModelValidationV1ExecutionResultScientificResponseSelectionV0.lean":
        "5cd2aef53c4f6ba463a8ac211580cfe24fd5f9203898bdbecc929b7897211c8a",
}

RADIUS_PAIRS_M = (
    (2e-3, 3e-3, "SMALL_ASYMMETRIC"),
    (5e-3, 5e-3, "PRODUCTION_EQUAL"),
    (5e-3, 1e-2, "LARGE_ASYMMETRIC"),
)
SURFACE_GAPS_M = (1e-4, 1e-3, 1e-2)
LAMBDA_ROLES = (
    ("SHORT_VS_GAP", lambda gap, radius: gap / 10.0),
    ("GAP_TRANSITION", lambda gap, radius: gap),
    ("RADIUS_TRANSITION", lambda gap, radius: radius),
    ("LONG_VS_GEOMETRY", lambda gap, radius: 10.0 * max(gap, radius)),
)
LEGACY_CASES = (
    (0.011, 1e-4, "LEGACY_STAGE_A_00"),
    (0.03, 5e-3, "LEGACY_STAGE_A_01"),
    (0.08, 0.1, "LEGACY_STAGE_A_02"),
)

PRINCIPAL_ROOT_CAUSE_OUTCOMES = (
    "IMPLEMENTATION_DEFECT_LOCALIZED",
    "FIXED_ORDER_CUBATURE_INADEQUATE",
    "REFERENCE_ORACLE_INADEQUATE",
    "NEAR_CONTACT_DOMAIN_DECOMPOSITION_REQUIRED",
    "ANGULAR_DFT_RESOLUTION_INDEPENDENTLY_INADEQUATE",
    "KERNEL_NOISE_DRIVES_DFT_FAILURE",
    "INTERNAL_APPARATUS_FORWARD_MODEL_NOT_ECONOMICALLY_VALIDATABLE",
)
ORACLE_AVAILABILITY_OUTCOMES = (
    "ANALYTIC_OR_REDUCED_SPHERE_ORACLE_AVAILABLE",
    "ANALYTIC_OR_REDUCED_SPHERE_ORACLE_NOT_VALIDATED",
)
PACKET_REVIEW_OUTCOMES = (
    "KERNEL_DIAGNOSIS_AND_REFERENCE_ORACLE_CONTRACT_READY",
    "BLOCKED_NONOVERLAP_ORACLE_DOMAIN",
    "BLOCKED_REFERENCE_ORACLE_CONTRACT",
    "BLOCKED_DIAGNOSTIC_GRID_CONTRACT",
    "BLOCKED_NEAR_CONTACT_LOCALIZATION_CONTRACT",
    "BLOCKED_DFT_ISOLATION_CONTRACT",
    "BLOCKED_DIAGNOSTIC_MUTATION_ROUTING",
    "BLOCKED_SCOPE_OR_PROVENANCE",
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _artifact_row(relative_path: str) -> dict[str, str]:
    return {"relative_path": relative_path, "sha256": _sha256(REPO_ROOT / relative_path)}


def _diagnostic_cases() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for radius_index, (r1, r2, radius_role) in enumerate(RADIUS_PAIRS_M):
        effective_radius = math.sqrt(r1 * r2)
        for gap_index, gap in enumerate(SURFACE_GAPS_M):
            for lambda_role, formula in LAMBDA_ROLES:
                lambda_m = formula(gap, effective_radius)
                rows.append({
                    "case_id": f"STRATIFIED_R{radius_index}_G{gap_index}_{lambda_role}",
                    "case_class": "STRATIFIED",
                    "radius_role": radius_role,
                    "radius_1_m": r1,
                    "radius_2_m": r2,
                    "effective_radius_m": effective_radius,
                    "surface_gap_m": gap,
                    "center_distance_m": r1 + r2 + gap,
                    "lambda_role": lambda_role,
                    "lambda_m": lambda_m,
                    "strictly_nonoverlapping": gap > 0.0,
                    "high_precision_anchor": (
                        radius_role == "PRODUCTION_EQUAL"
                        and lambda_role in {
                            "SHORT_VS_GAP", "GAP_TRANSITION", "RADIUS_TRANSITION"
                        }
                    ),
                })
    for distance, lambda_m, case_id in LEGACY_CASES:
        r1 = r2 = 5e-3
        gap = distance - r1 - r2
        rows.append({
            "case_id": case_id,
            "case_class": "LEGACY_STAGE_A_REPRODUCTION",
            "radius_role": "PRODUCTION_EQUAL",
            "radius_1_m": r1,
            "radius_2_m": r2,
            "effective_radius_m": 5e-3,
            "surface_gap_m": gap,
            "center_distance_m": distance,
            "lambda_role": "LEGACY_FROZEN",
            "lambda_m": lambda_m,
            "strictly_nonoverlapping": gap > 0.0,
            "high_precision_anchor": True,
        })
    return rows


def build_report() -> dict[str, Any]:
    for relative_path, expected in SELECTOR_HASHES.items():
        if _sha256(REPO_ROOT / relative_path) != expected:
            raise ValueError(f"selector authority drift: {relative_path}")
    selector = _load_json(SELECTOR_RELATIVE_PATH)
    if selector.get("selected_next_target") != TARGET:
        raise ValueError("selector did not authorize this packet preparation")
    if selector.get("selected_route") != (
        "BOUNDED_PRODUCTION_KERNEL_DIAGNOSIS_AND_REFERENCE_ORACLE"
    ):
        raise ValueError("selector route mismatch")
    if selector.get("scope", {}).get("kernel_diagnosis_executed") is not False:
        raise ValueError("selector unexpectedly executed a diagnosis")

    cases = _diagnostic_cases()
    if len(cases) != 39 or not all(row["strictly_nonoverlapping"] for row in cases):
        raise ValueError("diagnostic grid is not the frozen 39-case nonoverlap grid")
    preparation_gates = (
        "EXACT_SELECTOR_AUTHORITY_AND_TARGET",
        "ACCEPTED_STAGE_A_FAILURE_FROZEN",
        "PACKET_PREPARATION_ONLY_NO_DIAGNOSIS",
        "THIRTY_SIX_STRATIFIED_CASES_EXACT",
        "THREE_LEGACY_FAILURE_CASES_EXACT",
        "ALL_THIRTY_NINE_CASES_STRICTLY_NONOVERLAPPING",
        "THREE_RADIUS_PAIRS_AND_THREE_GAPS_EXACT",
        "FOUR_LAMBDA_REGIMES_EXACT",
        "NEWTONIAN_AND_YUKAWA_COMPONENTS_SEPARATE",
        "COMBINED_VALUE_AND_CANCELLATION_RATIO_REPORTED",
        "EXACT_NEWTONIAN_SHELL_ORACLE_FROZEN",
        "ANALYTIC_YUKAWA_FORM_FACTOR_ORACLE_FROZEN",
        "STABLE_SCALED_FORM_FACTOR_BRANCH_FROZEN",
        "FIXED_ORDER_PRODUCTION_PATH_FROZEN",
        "SEMI_ANALYTIC_RADIAL_REFERENCE_PATH_FROZEN",
        "ADAPTIVE_ARBITRARY_PRECISION_PATH_FROZEN",
        "REFERENCE_SELF_CONVERGENCE_AND_CROSS_ORACLE_RULES_FROZEN",
        "MAXIMUM_WORK_AND_FAIL_CLOSED_RULES_FROZEN",
        "NEAR_CONTACT_EXCESS_SEPARATION_PROFILE_FROZEN",
        "PRECISION_SUMMATION_SCALING_AND_SYMMETRY_PROBES_FROZEN",
        "PAIR_ENERGY_BEFORE_TORQUE_ORDER_FROZEN",
        "ANALYTIC_PRODUCTION_AND_FINITE_DIFFERENCE_TORQUE_PATHS_FROZEN",
        "EXACT_ANALYTIC_DFT_SIGNAL_AND_EXPECTED_COEFFICIENTS_FROZEN",
        "KNOWN_HIGH_HARMONIC_ALIAS_PROBE_FROZEN",
        "TEN_PRODUCTION_ROUTED_MUTATIONS_FROZEN",
        "MULTILABEL_ROOT_CAUSE_AND_PRIORITY_RULES_FROZEN",
        "ANALYTIC_ORACLE_AVAILABILITY_REPORTED_SEPARATELY",
        "DIAGNOSTIC_OUTPUTS_ONLY_FINAL_VECTOR_AND_JACOBIAN_FORBIDDEN",
        "ONE_DIAGNOSIS_ONLY_AFTER_INDEPENDENT_REVIEW",
        "NO_REPAIR_RERUN_V2_IDENTIFIABILITY_OR_STAGE_B_AUTHORITY",
    )

    scope = {
        "diagnosis_packet_prepared": True,
        "selector_authority_consumed": True,
        "diagnostic_case_grid_constructed_as_contract_metadata": True,
        "diagnosis_packet_independent_review_required": True,
        "diagnosis_execution_authorized": False,
        "diagnosis_executed": False,
        "production_kernel_called_during_preparation": False,
        "reference_oracle_called_during_preparation": False,
        "component_interaction_value_computed": False,
        "convergence_table_computed": False,
        "root_cause_classification_computed": False,
        "production_integration_method_changed": False,
        "implementation_corrected": False,
        "additional_stage_a_execution_authorized": False,
        "full_forward_model_rerun_authorized": False,
        "final_real_150_vector_authorized": False,
        "jacobian_authorized": False,
        "svd_authorized": False,
        "eta_lambda_authorized": False,
        "identifiability_classification_authorized": False,
        "stochastic_packet_preparation_authorized": False,
        "stage_b_eligible": False,
        "stage_b_authorized": False,
        "automatic_v2_authorized": False,
        "synthetic_noise_authorized": False,
        "sensitivity_forecast_authorized": False,
        "empirical_constraint_claimed": False,
        "numerical_alpha_bound_computed": False,
        "scalar_branch_adopted": False,
    }

    return {
        "schema_id": "toe.scalar_only_yukawa.sphere_kernel_diagnosis_and_reference_oracle.packet.v0",
        "packet_id": "SCALAR_ONLY_YUKAWA_SPHERE_KERNEL_DIAGNOSIS_AND_REFERENCE_ORACLE_PACKET_20260719_v0",
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
                "formal/python/tools/scalar_only_yukawa_sphere_kernel_"
                "diagnosis_and_reference_oracle_packet_v0.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
        },
        "accepted_failure_anchor": {
            "stage_a_execution_count": 1,
            "principal_result": "BLOCKED_PRODUCTION_KERNEL_VALIDATION",
            "production_vs_order24_error": 6.867902041407599e-2,
            "order16_vs_order24_error": 4.202776018628042e-1,
            "stage_a_cubature_tolerance": 1e-6,
            "angular_dft_256_vs_512_error": 1.481612456806414e-6,
            "stage_a_angular_dft_tolerance": 1e-8,
            "physical_identifiability": "NOT_TESTED",
            "stage_a_rerun": "NOT_AUTHORIZED",
        },
        "physical_constants_and_conventions": {
            "gravitational_constant_m3_kg_s2": 6.67430e-11,
            "yukawa_amplitude": 1.0 / 3.0,
            "density_kg_m3": 19250.0,
            "center_distance_definition": "D=R1+R2+g",
            "surface_gap_definition": "g=D-R1-R2",
            "nonoverlap_rule": "g>0",
            "energy_unit": "J",
            "torque_unit": "N_m",
            "angle_unit": "rad",
            "positive_lambda_required": True,
        },
        "diagnostic_domain": {
            "stratified_case_count": 36,
            "legacy_case_count": 3,
            "total_case_count": len(cases),
            "radius_pairs_m": [
                {"radius_1_m": r1, "radius_2_m": r2, "role": role}
                for r1, r2, role in RADIUS_PAIRS_M
            ],
            "surface_gaps_m": list(SURFACE_GAPS_M),
            "lambda_formulas": {
                "SHORT_VS_GAP": "g/10",
                "GAP_TRANSITION": "g",
                "RADIUS_TRANSITION": "sqrt(R1*R2)",
                "LONG_VS_GEOMETRY": "10*max(g,sqrt(R1*R2))",
            },
            "legacy_cases": [
                {"center_distance_m": distance, "lambda_m": lam, "case_id": case_id}
                for distance, lam, case_id in LEGACY_CASES
            ],
            "high_precision_anchor_count": sum(row["high_precision_anchor"] for row in cases),
            "rows": cases,
            "post_result_case_selection": "FORBIDDEN",
        },
        "component_contract": {
            "components": ["NEWTONIAN", "YUKAWA", "COMBINED_DIAGNOSTIC_ONLY"],
            "per_component_records": [
                "VALUE_J",
                "ABSOLUTE_ERROR_J",
                "RELATIVE_ERROR",
                "CONVERGENCE_BY_PATH_AND_LEVEL",
                "DIMENSIONAL_CHECK",
                "LIMITING_BEHAVIOR",
            ],
            "combined_records": ["VALUE_J", "CANCELLATION_RATIO"],
            "cancellation_ratio": "(abs(U_N)+abs(U_Y))/max(abs(U_N+U_Y),1e-300_J)",
            "combined_value_may_decide_component_accuracy": False,
            "newtonian_limits": ["U_N=-G*M1*M2/D", "D*U_N=-G*M1*M2"],
            "yukawa_limits": [
                "lambda_to_infinity_F_to_1_and_exp_to_1",
                "lambda_much_less_than_gap_U_Y_to_0",
            ],
        },
        "analytic_oracle_contract": {
            "domain": "STRICTLY_NONOVERLAPPING_HOMOGENEOUS_SPHERES_ONLY",
            "mass": "M_i=(4*pi/3)*rho_i*R_i^3",
            "newtonian": "U_N(D)=-G*M1*M2/D",
            "dimensionless_radius": "x_i=R_i/lambda",
            "sphere_form_factor": "F(x)=3*(x*cosh(x)-sinh(x))/x^3",
            "yukawa": "U_Y(D)=-A_Y*G*M1*M2*F(x1)*F(x2)*exp(-D/lambda)/D",
            "stable_scaled_factor": "H(x)=exp(-x)*F(x)=3*((x-1)+(x+1)*exp(-2*x))/(2*x^3)",
            "stable_yukawa": "U_Y=-A_Y*G*M1*M2*H(x1)*H(x2)*exp(-g/lambda)/D",
            "small_x_series": "F(x)=1+x^2/10+x^4/280+x^6/15120+O(x^8)",
            "small_x_branch_max": 1e-3,
            "independent_implementation_required": True,
            "production_form_factor_function_import_forbidden": True,
            "derivation_obligations": [
                "NEWTONIAN_SHELL_THEOREM_EXTERNAL_FIELD",
                "YUKAWA_SPHERE_EXTERNAL_FIELD_RADIAL_INTEGRATION",
                "TWO_SPHERE_NONOVERLAP_COMPOSITION",
                "PROJECT_NORMALIZATION_AND_A_Y_ONE_THIRD",
                "STABLE_SCALED_FACTOR_ALGEBRA",
            ],
        },
        "evaluation_paths": {
            "path_count": 4,
            "production_fixed_tensor": {
                "path_id": "P0_FROZEN_BINARY64_FOUR_DIMENSIONAL_GAUSS_LEGENDRE",
                "orders": [8, 12, 16, 24, 32, 48],
                "dimensions_refined_together": ["r1", "mu1", "r2", "mu2"],
                "summation": "PAIRWISE_NUMPY_BINARY64_AS_FROZEN",
                "all_39_cases": True,
                "scientific_role": "DIAGNOSED_PRODUCTION_PATH_NOT_REFERENCE_ORACLE",
            },
            "analytic_closed_form": {
                "path_id": "R1_INDEPENDENT_ANALYTIC_SHELL_AND_FORM_FACTOR",
                "precision_decimal_digits": 120,
                "all_39_cases": True,
                "scientific_role": "EXACT_CANDIDATE_ORACLE_SUBJECT_TO_DERIVATION_CONTROLS",
            },
            "semi_analytic_radial": {
                "path_id": "R2_HIGH_PRECISION_RADIAL_FORM_FACTOR_INTEGRAL",
                "formula": "F(x)=3/x^3*integral_0^x(t*sinh(t),dt)",
                "precision_decimal_digits": [50, 80, 120],
                "adaptive_method": "TANH_SINH",
                "all_39_cases": True,
                "scientific_role": "INDEPENDENT_REDUCED_REFERENCE",
            },
            "adaptive_direct_density": {
                "path_id": "R3_ADAPTIVE_ARBITRARY_PRECISION_DIRECT_FOUR_DIMENSIONAL_DENSITY",
                "coordinates": ["u1=r1/R1", "mu1", "u2=r2/R2", "mu2"],
                "precision_decimal_digits": [50, 80, 120],
                "tanh_sinh_max_degrees": [6, 8, 10],
                "anchor_case_count": sum(row["high_precision_anchor"] for row in cases),
                "scientific_role": "DIRECT_NUMERIC_CROSS_ORACLE_ON_FROZEN_ANCHORS",
            },
            "nearby_order_same_path_is_independent_oracle": False,
        },
        "oracle_convergence_and_work_contract": {
            "plateau_levels": ["80_DIGITS_DEGREE_8", "120_DIGITS_DEGREE_10"],
            "absolute_energy_tolerance_J": 1e-36,
            "relative_energy_tolerance": 1e-10,
            "plateau_rule": "abs(last-prev)<=1e-36_J+1e-10*abs(last)",
            "cross_oracle_rule": "abs(R_i-R_j)<=1e-36_J+1e-10*abs(R1_ANALYTIC)",
            "production_accuracy_rule": "abs(P-R)<=1e-36_J+1e-6*abs(R)",
            "reference_must_plateau_before_judging_production": True,
            "higher_cost_alone_implies_correctness": False,
            "failed_reference_plateau_outcome": "REFERENCE_ORACLE_INADEQUATE",
            "maximum_function_evaluations_per_direct_anchor": 2_000_000,
            "maximum_wall_clock_seconds_per_direct_anchor": 180,
            "maximum_total_wall_clock_seconds": 3600,
            "maximum_memory_mib": 4096,
            "budget_exhaustion_behavior": "FAIL_CLOSED_REFERENCE_ORACLE_INADEQUATE",
            "result_dependent_tolerance_or_budget_change": "FORBIDDEN",
        },
        "near_contact_contract": {
            "point_pair_separation": "s=norm(x1-x2)",
            "minimum_separation": "s_min=g",
            "excess_coordinate": "chi=(s-g)/max(g,lambda)",
            "chi_bin_edges": [0.0, 0.25, 1.0, 4.0, "INF"],
            "records": [
                "SIGNED_ENERGY_FRACTION_BY_CHI_BIN",
                "ABSOLUTE_INTEGRAND_FRACTION_BY_CHI_BIN",
                "NODE_FRACTION_BY_CHI_BIN",
                "LOCAL_KERNEL_MAX_MIN_RATIO_BY_CHI_BIN",
            ],
            "dominant_near_contact_rule": "absolute_fraction_chi_le_1>=0.90",
            "domain_decomposition_probe": {
                "chi_boundaries": [0.25, 1.0, 4.0],
                "independent_adaptation_per_subdomain": True,
                "required_improvement_factor": 10.0,
                "classification": "NEAR_CONTACT_DOMAIN_DECOMPOSITION_REQUIRED",
            },
            "global_normalization_signature": (
                "error_nearly_constant_across_gap_lambda_and_refinement_and_"
                "matches_one_frozen_mutation_fingerprint"
            ),
        },
        "precision_summation_and_symmetry_contract": {
            "precision_levels": ["IEEE_BINARY64", "MP_50_DIGITS", "MP_80_DIGITS", "MP_120_DIGITS"],
            "summation_methods": ["ORDINARY", "PAIRWISE", "KAHAN", "MATH_FSUM_OR_MP_EXACT_ACCUMULATION"],
            "component_evaluation_modes": ["SEPARATE_U_N_AND_U_Y", "DIRECT_COMBINED_DIAGNOSTIC_ONLY"],
            "coordinate_modes": ["RAW_SI", "NONDIMENSIONALIZED_BY_MAX_D_R1_R2_LAMBDA"],
            "energy_scale": "G*rho1*rho2*R1^3*R2^3/D",
            "symmetry_modes": ["AZIMUTH_ANALYTICALLY_REDUCED", "EXPLICIT_AZIMUTH_CONTROL"],
            "explicit_azimuth_control": {
                "case_ids": ["LEGACY_STAGE_A_00", "LEGACY_STAGE_A_01", "LEGACY_STAGE_A_02"],
                "radial_polar_order": 12,
                "azimuth_sample_counts": [32, 64],
                "acceptance_rule": "abs(reduced-unreduced)<=1e-34_J+1e-8*abs(reduced)",
            },
            "roundoff_dominance_rule": "precision_change_improves_error_by_at_least_100x_while_method_and_domain_are_fixed",
        },
        "torque_isolation_contract": {
            "execution_order": "PAIR_ENERGY_ORACLES_MUST_PASS_BEFORE_TORQUE_TESTS",
            "gaps_m": [1e-4, 1e-3, 1e-2],
            "lambda_m": [1e-4, 1e-3, 1e-2],
            "angles_rad": [math.pi / 7.0, 3.0 * math.pi / 10.0],
            "component_modes": ["NEWTONIAN", "YUKAWA"],
            "torque_paths": [
                "ANALYTIC_PAIR_ENERGY_DERIVATIVE",
                "FROZEN_PRODUCTION_FORCE_LEVER_ROUTE",
                "FIVE_POINT_ENERGY_FINITE_DIFFERENCE_CHECK",
            ],
            "finite_difference_steps_rad": [1e-3, 5e-4, 2.5e-4, 1.25e-4],
            "acceptance_rule": "abs(delta_tau)<=1e-22_N_m+1e-8*abs(tau_oracle)",
            "finite_difference_refinement_required": True,
            "final_apparatus_harmonic_vector_prohibited": True,
        },
        "angular_dft_contract": {
            "convention": "c_n=(1/N)*sum_k(tau(theta_k)*exp(-i*n*theta_k))",
            "theta_grid": "theta_k=2*pi*k/N",
            "sample_counts": [32, 64, 128, 256, 512, 1024],
            "retained_harmonics": [2, 4, 6],
            "analytic_signal": {
                "formula": "sum_n A_n*cos(n*theta+phi_n)",
                "rows": [
                    {"n": 2, "amplitude_N_m": 2e-15, "phase_rad": math.pi / 7.0},
                    {"n": 4, "amplitude_N_m": 7e-16, "phase_rad": -math.pi / 9.0},
                    {"n": 6, "amplitude_N_m": 3e-16, "phase_rad": math.pi / 11.0},
                ],
                "expected_coefficient": "c_n=(A_n/2)*exp(i*phi_n)",
                "absolute_tolerance_N_m": 1e-28,
                "relative_tolerance": 1e-12,
            },
            "alias_probe": {
                "harmonic": 258,
                "amplitude_N_m": 1e-16,
                "phase_rad": math.pi / 13.0,
                "required_finding": "ALIASES_IN_N256_BUT_NOT_IN_RETAINED_N512_COEFFICIENTS",
            },
            "production_torque_test_gate": "PAIR_ENERGY_AND_TORQUE_ORACLES_PASS_FIRST",
            "production_sample_counts": [128, 256, 512, 1024],
            "classification_rule": {
                "analytic_fails": "ANGULAR_DFT_RESOLUTION_INDEPENDENTLY_INADEQUATE",
                "analytic_passes_production_fails": "KERNEL_NOISE_DRIVES_DFT_FAILURE",
            },
        },
        "mutation_controls": {
            "mutation_count": 10,
            "production_diagnostic_path_required": True,
            "rows": [
                {"mutation_id": "REMOVE_ONE_RADIAL_VOLUME_FACTOR_R_SQUARED", "designated_control": "NEWTONIAN_SHELL_ORACLE_AND_DIMENSIONAL_CHECK"},
                {"mutation_id": "INTERPRET_RADIUS_AS_DIAMETER", "designated_control": "MASS_AND_NONOVERLAP_GEOMETRY_ORACLE"},
                {"mutation_id": "USE_SURFACE_GAP_AS_CENTER_DISTANCE", "designated_control": "CENTER_DISTANCE_AND_NEWTONIAN_SHELL_ORACLE"},
                {"mutation_id": "REPLACE_A_Y_ONE_THIRD_BY_ONE", "designated_control": "YUKAWA_ANALYTIC_ORACLE"},
                {"mutation_id": "FLIP_YUKAWA_EXPONENTIAL_SIGN", "designated_control": "SHORT_RANGE_LIMIT_AND_YUKAWA_ORACLE"},
                {"mutation_id": "FLIP_NEGATIVE_ANGULAR_ENERGY_DERIVATIVE_SIGN", "designated_control": "TORQUE_THREE_PATH_COMPARISON"},
                {"mutation_id": "LEAVE_MU2_AT_ORDER_8_WHILE_OTHER_DIMENSIONS_REFINE", "designated_control": "ALL_DIMENSION_REFINEMENT_CUSTODY"},
                {"mutation_id": "REMOVE_ONE_SPHERE_FORM_FACTOR", "designated_control": "YUKAWA_ANALYTIC_AND_RADIAL_ORACLES"},
                {"mutation_id": "DOUBLE_DFT_NORMALIZATION", "designated_control": "ANALYTIC_DFT_COEFFICIENT_ORACLE"},
                {"mutation_id": "REVERSE_DFT_PHASE_SIGN", "designated_control": "ANALYTIC_DFT_PHASE_ORACLE"},
            ],
            "acceptance": "ALL_TEN_MUTATIONS_MUST_FAIL_THEIR_DESIGNATED_PRODUCTION_ROUTED_CONTROL",
            "test_only_substitute_path": "FORBIDDEN",
        },
        "root_cause_adjudication": {
            "multilabel_reporting": True,
            "principal_priority": [
                "REFERENCE_ORACLE_INADEQUATE",
                "IMPLEMENTATION_DEFECT_LOCALIZED",
                "NEAR_CONTACT_DOMAIN_DECOMPOSITION_REQUIRED",
                "FIXED_ORDER_CUBATURE_INADEQUATE",
                "ANGULAR_DFT_RESOLUTION_INDEPENDENTLY_INADEQUATE",
                "KERNEL_NOISE_DRIVES_DFT_FAILURE",
                "INTERNAL_APPARATUS_FORWARD_MODEL_NOT_ECONOMICALLY_VALIDATABLE",
            ],
            "principal_outcomes": list(PRINCIPAL_ROOT_CAUSE_OUTCOMES),
            "oracle_availability_outcomes": list(ORACLE_AVAILABILITY_OUTCOMES),
            "implementation_defect_requires": (
                "one_specific_mutation_fingerprint_matches_and_independent_"
                "oracle_passes_and_error_is_not_removed_by_valid_refinement"
            ),
            "fixed_order_inadequate_requires": (
                "oracle_passes_and_last_three_fixed_orders_improve_monotonically_"
                "but_order48_fails_accuracy_or_cost_rule"
            ),
            "near_contact_requires": (
                "chi_le_1_absolute_fraction_at_least_0.90_and_decomposition_"
                "improves_error_at_least_10x"
            ),
            "reference_inadequate_requires": "any_required_oracle_plateau_or_cross_oracle_check_fails",
            "economic_failure_requires": (
                "validated_error_extrapolation_cannot_reach_tolerance_within_"
                "frozen_3600_s_4096_MiB_budget"
            ),
            "no_root_cause_rounding": "UNRESOLVED_IF_NO_FROZEN_PREDICATE_IS_SATISFIED",
        },
        "work_packages": {
            "count": 9,
            "rows": [
                "WP1_NONOVERLAP_GEOMETRY_AND_DIMENSIONAL_CUSTODY",
                "WP2_NEWTONIAN_COMPONENT_ORACLE",
                "WP3_YUKAWA_ANALYTIC_AND_RADIAL_ORACLES",
                "WP4_ADAPTIVE_DIRECT_HIGH_PRECISION_ANCHORS",
                "WP5_FIXED_ORDER_AND_NEAR_CONTACT_PROFILES",
                "WP6_PRECISION_SUMMATION_SCALING_AND_SYMMETRY",
                "WP7_PAIR_ENERGY_TO_TORQUE_ISOLATION",
                "WP8_ANALYTIC_AND_PRODUCTION_DFT_ISOLATION",
                "WP9_ROOT_CAUSE_COST_AND_METHOD_RECOMMENDATION",
            ],
            "executed_count": 0,
        },
        "authorized_diagnostic_outputs": [
            "COMPONENT_LEVEL_INTERACTION_VALUES",
            "EXACT_OR_HIGH_PRECISION_REFERENCE_VALUES",
            "CONVERGENCE_TABLES",
            "ERROR_VS_GAP_RANGE_AND_RADIUS",
            "NEAR_CONTACT_CONTRIBUTION_PROFILES",
            "PRECISION_SUMMATION_SCALING_AND_SYMMETRY_COMPARISONS",
            "TORQUE_DERIVATIVE_COMPARISONS",
            "ANALYTIC_AND_PRODUCTION_DFT_REFINEMENT",
            "ROOT_CAUSE_CLASSIFICATION",
            "RECOMMENDED_REPLACEMENT_METHOD_AND_ESTIMATED_COST",
        ],
        "forbidden_outputs": [
            "FINAL_REAL_150_APPARATUS_VECTOR",
            "SEVENTEEN_COLUMN_JACOBIAN",
            "SINGULAR_VALUES",
            "ETA_LAMBDA",
            "IDENTIFIABILITY_RESULT",
            "SYNTHETIC_NOISE",
            "SENSITIVITY_FORECAST",
            "SCALAR_RANGE_OR_ALPHA_CONCLUSION",
        ],
        "packet_review_contract": {
            "independent_review_required": True,
            "review_outcomes": list(PACKET_REVIEW_OUTCOMES),
            "ready_outcome_authorizes": "ONE_BOUNDED_DIAGNOSIS_EXECUTION_ONLY",
            "ready_outcome_does_not_authorize": [
                "INTEGRATION_REPLACEMENT",
                "IMPLEMENTATION_CORRECTION_AND_IMMEDIATE_RERUN",
                "STAGE_A_REOPENING",
                "V2",
                "IDENTIFIABILITY",
                "STAGE_B",
            ],
            "post_diagnosis_independent_result_review_required": True,
            "post_diagnosis_fresh_selector_required": True,
        },
        "preparation_gates": {
            "gate_count": len(preparation_gates),
            "pass_count": len(preparation_gates),
            "failure_count": 0,
            "rows": [{"gate_id": gate, "status": "PASS"} for gate in preparation_gates],
        },
        "scope": scope,
        "claim_ceiling": (
            "This packet preregisters one bounded diagnostic contract. It performs "
            "no kernel, oracle, torque, harmonic, cost, or root-cause calculation; "
            "changes no production implementation; authorizes no execution before "
            "independent review; and does not reopen Stage A or Stage B."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_report(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Prepare the bounded Yukawa sphere-kernel diagnosis packet without executing it.")
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
        print("sphere-kernel diagnosis packet artifact missing or stale")
        return 1
    print("sphere-kernel diagnosis packet OK gates=30/30 execution=0/9")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
