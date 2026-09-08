from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_"
    "FORWARD_MODEL_VALIDATION_PACKET_20260718_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_"
    "FORWARD_MODEL_VALIDATION_PACKET_20260718_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_scalar_only_yukawa_deterministic_torsion_balance_"
    "forward_model_validation_packet_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ScalarOnlyYukawaDeterministicTorsionBalanceForwardModelValidationPacketV0.lean"
)
SELECTION_RELATIVE_PATH = (
    "formal/docs/release/POST_SCALAR_ONLY_YUKAWA_SYNTHETIC_FORECAST_PACKET_"
    "REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260718_v0.json"
)

TARGET = (
    "prepare_scalar_only_yukawa_deterministic_torsion_balance_"
    "forward_model_validation_packet_v0"
)
VERDICT = (
    "PREPARED_DETERMINISTIC_FORWARD_MODEL_VALIDATION_CONTRACT_"
    "PENDING_INDEPENDENT_REVIEW"
)
PROVISIONAL_READINESS = "DETERMINISTIC_FORWARD_MODEL_VALIDATION_CONTRACT_READY"
SELECTED_NEXT_TARGET = (
    "review_scalar_only_yukawa_deterministic_torsion_balance_"
    "forward_model_validation_packet_v0_result"
)
SELECTED_NEXT_TARGET_KIND = "INDEPENDENT_DETERMINISTIC_FORWARD_MODEL_PACKET_REVIEW_ONLY"

AUTHORITY_HASHES = {
    "formal/docs/lanes/POST_SCALAR_ONLY_YUKAWA_SYNTHETIC_FORECAST_PACKET_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260718_v0.md":
        "eecfa86d0c73cbf5e6e4630cba7c4833b0393267fd187124c56b2f0b5b57d174",
    SELECTION_RELATIVE_PATH:
        "b43c7b5689734fb43ef5de6e56e8ff11b8a0edc606e6071cfa67fee1fb76995e",
    "formal/python/tools/post_scalar_only_yukawa_synthetic_forecast_packet_review_scientific_response_selection_v0.py":
        "bc363ac1d787de31af27b056d71f8631f092603297b44a86952a554e83f0daf9",
    "formal/python/tests/test_post_scalar_only_yukawa_synthetic_forecast_packet_review_scientific_response_selection_v0.py":
        "0d0be28092a3ff0c65ccf6158ab32dde11fb36a1c415c7a2bbd40773320dac9b",
    "formal/toe_formal/ToeFormal/Derivation/PostScalarOnlyYukawaSyntheticForecastPacketReviewScientificResponseSelectionV0.lean":
        "d88726bf3cfc83878a638283fa8e23bcac8a09daafa1034bfa3245ff2d757964",
}

PACKET_REVIEW_OUTCOMES = (
    "DETERMINISTIC_FORWARD_MODEL_VALIDATION_CONTRACT_READY",
    "BLOCKED_HARMONIC_CONVENTION_INCOMPLETE",
    "BLOCKED_PRODUCTION_KERNEL_VALIDATION",
    "BLOCKED_TORQUE_DERIVATIVE_CONTRACT",
    "BLOCKED_GEOMETRY_OR_SYMMETRY_FAILURE",
    "BLOCKED_NUMERICAL_CONVERGENCE",
    "BLOCKED_DETERMINISTIC_NUISANCE_MAPPING",
    "BLOCKED_PARAMETER_IDENTIFIABILITY",
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


def _rows(names: list[str], status: str) -> list[dict[str, str]]:
    return [{"item_id": name, "status": status} for name in names]


def build_packet() -> dict[str, Any]:
    for relative_path, expected_hash in AUTHORITY_HASHES.items():
        if _sha256(REPO_ROOT / relative_path) != expected_hash:
            raise ValueError(f"deterministic packet authority drift: {relative_path}")
    selection = _load_json(SELECTION_RELATIVE_PATH)
    if selection.get("verdict") != (
        "SELECTED_DETERMINISTIC_FORWARD_MODEL_VALIDATION_PACKET_PREPARATION"
    ):
        raise ValueError("deterministic response-selection verdict mismatch")
    if selection.get("selected_next_target") != TARGET:
        raise ValueError("response selection did not authorize this packet")

    work_packages = _rows([
        "EXACT_HARMONIC_CONVENTION",
        "SHARED_PRODUCTION_KERNEL",
        "ENERGY_TO_TORQUE_CROSS_VALIDATION",
        "FOUR_ANALYTIC_BENCHMARKS",
        "APPARATUS_HARMONIC_AND_SYMMETRY_VALIDATION",
        "MUTATION_AND_PHASE_SIGN_CONTROLS",
        "NUMERICAL_CONVERGENCE",
        "DETERMINISTIC_PERTURBATION_MAPS",
        "JACOBIAN_IDENTIFIABILITY",
        "CANONICAL_REAL_150_OUTPUT",
    ], "NOT_EXECUTED")
    execution_controls = _rows([
        "POINT_NEWTONIAN_BENCHMARK",
        "POINT_YUKAWA_BENCHMARK",
        "UNIFORM_SPHERE_FORM_FACTOR_BENCHMARK",
        "APPARATUS_TORQUE_SYMMETRY_BENCHMARK",
        "MUTATE_YUKAWA_SIGN",
        "MUTATE_FIXED_AMPLITUDE",
        "MUTATE_SPHERE_FORM_FACTOR",
        "MUTATE_TORQUE_SIGN",
        "MUTATE_DFT_NORMALIZATION",
        "ODD_AND_COSINE_SYMMETRY_ZEROS",
        "PHASE_AND_ANGLE_REVERSAL",
        "FORCE_LEVER_TORQUE_CROSS_CHECK",
        "ENERGY_FINITE_DIFFERENCE_TORQUE_CROSS_CHECK",
        "REFINEMENT_AND_REPEATED_SERIALIZATION",
        "JACOBIAN_RANK_AND_SCALAR_SHAPE_IDENTIFIABILITY",
    ], "NOT_EXECUTED")
    output_classes = _rows([
        "NEWTONIAN_REAL_150_VECTOR",
        "TWENTY_FIVE_YUKAWA_REAL_150_VECTORS",
        "REFERENCE_TOTAL_REAL_150_VECTOR",
        "DETERMINISTIC_PERTURBATION_RESPONSE_VECTORS",
        "JACOBIAN_SVD_RANK_CORRELATION_AND_ETA_TABLES",
    ], "NOT_PRODUCED")
    benchmarks = [
        {"benchmark_id": "POINT_NEWTONIAN", "status": "NOT_EXECUTED"},
        {"benchmark_id": "POINT_YUKAWA", "status": "NOT_EXECUTED"},
        {"benchmark_id": "UNIFORM_SPHERE_FORM_FACTOR", "status": "NOT_EXECUTED"},
        {"benchmark_id": "APPARATUS_TORQUE_AND_SYMMETRY", "status": "NOT_EXECUTED"},
    ]
    mutations = [
        {"mutation_id": "FLIP_YUKAWA_ENERGY_SIGN", "expected_result": "DESIGNATED_CONTROL_FAILS"},
        {"mutation_id": "REPLACE_ONE_THIRD_BY_ONE", "expected_result": "DESIGNATED_CONTROL_FAILS"},
        {"mutation_id": "REMOVE_ONE_SPHERE_FORM_FACTOR", "expected_result": "DESIGNATED_CONTROL_FAILS"},
        {"mutation_id": "FLIP_NEGATIVE_ENERGY_DERIVATIVE_TORQUE_SIGN", "expected_result": "DESIGNATED_CONTROL_FAILS"},
        {"mutation_id": "DOUBLE_DFT_NORMALIZATION", "expected_result": "DESIGNATED_CONTROL_FAILS"},
    ]
    symmetry = [
        "ODD_HARMONICS_1_3_5_ZERO",
        "NOMINAL_EVEN_COSINE_QUADRATURES_ZERO",
        "EVEN_SINE_2_4_6_NONZERO_WHEN_IDENTIFIABLE",
        "TORQUE_ZERO_AT_FOUR_SYMMETRY_ANGLES",
        "ANGLE_REVERSAL_CONJUGATES_COEFFICIENTS",
        "RIGID_PI_OVER_16_ROTATION_PHASE_LAW",
        "NEWTONIAN_AND_YUKAWA_DISTANCE_SCALING",
    ]
    perturbations = [
        ("TORQUE_CALIBRATION", "fraction", 0.0, [-0.02, 0.02], "multiply final torque by 1+k_tau"),
        ("SOURCE_DENSITY_SCALE", "fraction", 0.0, [-0.01, 0.01], "rho_A -> rho_A*(1+k_A)"),
        ("DETECTOR_DENSITY_SCALE", "fraction", 0.0, [-0.01, 0.01], "rho_D -> rho_D*(1+k_D)"),
        ("DETECTOR_LEVER_OFFSET", "m", 0.0, [-1e-4, 1e-4], "L_D -> L_D+dL_D"),
        ("ATTRACTOR_LEVER_OFFSET", "m", 0.0, [-1e-4, 1e-4], "L_A -> L_A+dL_A"),
        ("GAP_OFFSET", "m", 0.0, [-1e-5, 1e-5], "d_j -> d_j+dd with positive-gap guard"),
        ("ATTRACTOR_AXIS_X_OFFSET", "m", 0.0, [-1e-4, 1e-4], "add dx to every attractor center x"),
        ("ATTRACTOR_AXIS_Y_OFFSET", "m", 0.0, [-1e-4, 1e-4], "add dy to every attractor center y"),
        ("ANGULAR_ZERO_OFFSET", "rad", 0.0, [-1e-3, 1e-3], "evaluate geometry at theta-dtheta"),
        ("HARMONIC_LEAKAGE", "fraction", 0.0, [-0.002, 0.002], "z -> (I+ell*L_adjacent)*z"),
        ("BACKGROUND_2RE", "N_m", 0.0, [-1e-17, 1e-17], "add constant to 2RE at every gap"),
        ("BACKGROUND_2IM", "N_m", 0.0, [-1e-17, 1e-17], "add constant to 2IM at every gap"),
        ("BACKGROUND_4RE", "N_m", 0.0, [-1e-17, 1e-17], "add constant to 4RE at every gap"),
        ("BACKGROUND_4IM", "N_m", 0.0, [-1e-17, 1e-17], "add constant to 4IM at every gap"),
        ("BACKGROUND_6RE", "N_m", 0.0, [-1e-17, 1e-17], "add constant to 6RE at every gap"),
        ("BACKGROUND_6IM", "N_m", 0.0, [-1e-17, 1e-17], "add constant to 6IM at every gap"),
    ]
    perturbation_rows = [
        {"perturbation_id": pid, "unit": unit, "nominal": nominal, "test_range": limits, "exact_map": mapping}
        for pid, unit, nominal, limits, mapping in perturbations
    ]
    control_ids = [
        "EXACT_RESPONSE_SELECTION_AUTHORITY_AND_TARGET",
        "STAGE_A_ONLY_SCOPE_RETAINED",
        "FIXED_ONE_THIRD_COMPARISON_PROVENANCE",
        "APPARATUS_GEOMETRY_AND_SI_CONSTANTS_EXACT",
        "ONE_SHARED_PRODUCTION_FUNCTION_CHAIN",
        "STABLE_UNIFORM_SPHERE_FORM_FACTOR_EVALUATION",
        "ANALYTIC_NEGATIVE_ENERGY_DERIVATIVE_TORQUE",
        "TWO_INDEPENDENT_TORQUE_CROSS_CHECKS",
        "EXACT_CONTINUOUS_AND_DISCRETE_HARMONIC_CONVENTION",
        "REAL_150_GAP_MAJOR_VECTOR_ORDER",
        "FOUR_PRODUCTION_ROUTED_BENCHMARKS",
        "FIVE_DELIBERATE_MUTATIONS_FAIL_DESIGNATED_CONTROLS",
        "SEVEN_SYMMETRY_PHASE_AND_SCALING_CONTROLS",
        "ANGULAR_REFINEMENT_AND_NEAR_ZERO_FLOOR",
        "REDUCED_DENSITY_CUBATURE_REFINEMENT",
        "ENERGY_DERIVATIVE_STEP_LADDER",
        "BIT_IDENTICAL_REPEAT_SERIALIZATION",
        "SIXTEEN_DETERMINISTIC_PERTURBATION_MAPS",
        "NO_STOCHASTIC_PRIORS_IN_STAGE_A",
        "VALID_PHYSICAL_DOMAIN_GUARDS",
        "SEVENTEEN_COLUMN_STANDARDIZED_JACOBIAN",
        "SVD_RANK_AND_PAIRWISE_DEGENERACY_RULES",
        "SCALAR_SHAPE_RESIDUAL_ETA_RULE",
        "FIVE_CONTIGUOUS_IDENTIFIABLE_RANGE_REQUIREMENT",
        "EXPECTED_EXACT_AMPLITUDE_DEGENERACY_DISCLOSED",
        "CANONICAL_CSV_JSON_AND_SHA256_CONTRACT",
        "TEN_WORK_PACKAGES_UNEXECUTED",
        "FIFTEEN_EXECUTION_CONTROLS_UNEXECUTED",
        "NINE_PACKET_REVIEW_OUTCOMES_FROZEN",
        "NO_EXECUTION_STOCHASTIC_EMPIRICAL_OR_THEORY_ADOPTION",
    ]
    scope = {
        "packet_preparation_executed": True,
        "exact_harmonic_convention_frozen": True,
        "shared_production_kernel_frozen": True,
        "analytic_torque_and_cross_checks_frozen": True,
        "benchmark_mutation_and_symmetry_controls_frozen": True,
        "convergence_contract_frozen": True,
        "deterministic_perturbation_maps_frozen": True,
        "jacobian_identifiability_contract_frozen": True,
        "canonical_serialization_frozen": True,
        "independent_packet_review_executed": False,
        "deterministic_execution_authorized": False,
        "deterministic_execution_performed": False,
        "benchmark_executed": False,
        "mutation_executed": False,
        "deterministic_vector_produced": False,
        "jacobian_computed": False,
        "stochastic_packet_preparation_authorized": False,
        "gaussian_noise_used": False,
        "covariance_used": False,
        "monte_carlo_executed": False,
        "profile_likelihood_executed": False,
        "sensitivity_forecast_produced": False,
        "synthetic_dataset_generated": False,
        "empirical_constraint_claimed": False,
        "numerical_lambda_bound_computed": False,
        "numerical_alpha_bound_computed": False,
        "alpha_sign_or_value_adopted": False,
        "scalar_branch_adopted": False,
        "native_scalar_bridge_identified": False,
        "native_gravitational_principle_identified": False,
        "gravitational_action_selected": False,
        "outbound_contact_authorized": False,
        "private_data_dependency_created": False,
    }
    return {
        "schema_id": "toe.scalar_only_yukawa.deterministic_torsion_balance_forward_model_validation.packet.v0",
        "packet_id": "SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_FORWARD_MODEL_VALIDATION_PACKET_20260718_v0",
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "provisional_readiness": PROVISIONAL_READINESS,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_response_selection_verdict": selection["verdict"],
            "frozen_response_selection_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in AUTHORITY_HASHES.items()
            ],
            "human_packet": _artifact_row(HUMAN_RELATIVE_PATH),
            "generator": _artifact_row("formal/python/tools/scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_packet_v0.py"),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
        },
        "stage_a_boundary": {
            "result_type": "DETERMINISTIC_FORWARD_MODEL_VALIDATION_CONTRACT",
            "gaussian_noise": "NONE",
            "covariance": "NONE",
            "monte_carlo_trials": "NONE",
            "profile_likelihood": "NONE",
            "sensitivity_forecast": "NONE",
            "execution": "NOT_AUTHORIZED",
        },
        "comparison_and_geometry": {
            "fixed_A_Y": "1/3",
            "G_SI": 6.67430e-11,
            "density_kg_m3": 19250.0,
            "detector_radius_m": 5e-3,
            "attractor_radius_m": 5e-3,
            "detector_lever_m": 3e-2,
            "attractor_lever_m": 3e-2,
            "gap_count": 25,
            "gap_grid": "LOGSPACE_1E-4_TO_1E-2_M",
            "positive_lambda_count": 25,
            "lambda_grid": "LOGSPACE_1E-5_TO_1E-1_M",
            "lambda_reference_m": 1e-3,
            "all_pairs_nonoverlapping": True,
            "not_eotwash_reconstruction": True,
        },
        "production_path": {
            "shared_functions": [
                "pair_distance",
                "pair_energy_and_radial_derivative",
                "apparatus_energy",
                "analytic_energy_derivative_torque",
                "discrete_harmonic_transform",
                "real_150_vector",
            ],
            "shared_function_count": 6,
            "uniform_sphere_form_factor": "F(x)=3*(x*cosh(x)-sinh(x))/x^3",
            "scaled_form_factor": "H(x)=exp(-x)*F(x)=3*((x-1)+(x+1)*exp(-2*x))/(2*x^3)",
            "small_x_series_threshold": 1e-3,
            "production_torque": "ANALYTIC_NEGATIVE_ENERGY_DERIVATIVE",
            "cross_checks": ["DIRECT_PAIR_FORCE_LEVER_ARM", "FIVE_POINT_CENTRAL_ENERGY_DERIVATIVE"],
            "benchmark_only_kernel_allowed": False,
        },
        "harmonic_contract": {
            "positive_angle": "COUNTERCLOCKWISE_ABOUT_PLUS_Z_VIEWED_FROM_PLUS_Z",
            "zero_angle": "ATTRACTOR_AND_DETECTOR_AXES_ALONG_PLUS_X",
            "positive_torque": "ABOUT_PLUS_Z",
            "coefficient": "c_n=(1/(2*pi))*integral(tau*exp(-i*n*theta),theta=0..2*pi)",
            "a_n_relation": "a_n=2*Re(c_n)",
            "b_n_relation": "b_n=-2*Im(c_n)",
            "discrete_coefficient": "c_n=(1/N)*sum_k(tau_k*exp(-i*n*2*pi*k/N))",
            "production_sample_count": 256,
            "retained_harmonics": [2, 4, 6],
            "ordering": "GAP_MAJOR_2RE_2IM_4RE_4IM_6RE_6IM",
            "real_vector_length": 150,
            "unit": "N_m",
        },
        "analytic_benchmarks": benchmarks,
        "deliberate_mutations": mutations,
        "symmetry_phase_controls": symmetry,
        "convergence_contract": {
            "error_definition": "abs(y-y_ref)/max(abs(y_ref),1e-22_N_m)",
            "torque_floor_N_m": 1e-22,
            "angular_samples": [128, 256, 512],
            "angular_relative_tolerance": 1e-8,
            "density_cubature_orders": [8, 12, 16, 24],
            "density_relative_tolerance": 1e-6,
            "force_lever_relative_tolerance": 1e-10,
            "energy_derivative_steps_rad": [1e-3, 5e-4, 2.5e-4, 1.25e-4],
            "energy_derivative_relative_tolerance": 1e-8,
            "canonical_repeat_bytes_identical": True,
            "fail_closed": True,
        },
        "deterministic_perturbations": {
            "count": len(perturbation_rows),
            "stochastic_priors": "NONE",
            "transformation_order": "GEOMETRY_DENSITY_ENERGY_TORQUE_HARMONICS_CALIBRATION_LEAKAGE_BACKGROUND",
            "rows": perturbation_rows,
        },
        "jacobian_identifiability_contract": {
            "parameter_order": ["LOG_LAMBDA"] + [row["perturbation_id"] for row in perturbation_rows],
            "row_count": 150,
            "column_count": 17,
            "derivative_method": "CENTERED_DIFFERENCE_WITH_HALF_STEP_CHECK_EXCEPT_EXACT_LINEAR_COLUMNS",
            "column_standardization": "FROZEN_TEST_SCALE",
            "global_output_scale": "MAX_ABS_NEWTONIAN_COMPONENT_WITH_1E-30_N_M_FAIL_FLOOR",
            "rank_relative_singular_value_threshold": 1e-10,
            "exact_projection_residual_threshold": 1e-10,
            "near_degenerate_absolute_correlation_threshold": 0.999,
            "identifiable_eta_threshold": 1e-3,
            "indistinguishable_eta_threshold": 1e-6,
            "minimum_contiguous_identifiable_lambda_points": 5,
            "expected_exact_amplitude_degeneracy": [
                "TORQUE_CALIBRATION",
                "SOURCE_DENSITY_SCALE",
                "DETECTOR_DENSITY_SCALE",
            ],
            "failure_outcome": "BLOCKED_PARAMETER_IDENTIFIABILITY",
        },
        "canonical_serialization": {
            "table_encoding": "UTF8_LF_CSV",
            "float_format": "SIGNED_SCIENTIFIC_17_DIGITS_AFTER_DECIMAL",
            "ordering": "GAP_MAJOR",
            "manifest": "SORTED_KEY_UTF8_JSON",
            "hash": "SHA256",
            "repeat_requirement": "BYTE_IDENTICAL",
        },
        "work_packages": work_packages,
        "execution_controls": execution_controls,
        "canonical_output_classes": output_classes,
        "packet_review_outcomes": list(PACKET_REVIEW_OUTCOMES),
        "preparation_controls": {
            "control_count": len(control_ids),
            "pass_count": len(control_ids),
            "failure_count": 0,
            "rows": [{"control_id": cid, "status": "PASS"} for cid in control_ids],
        },
        "scope": scope,
        "current_posture": {
            "stage_a_packet": "PREPARED_PENDING_INDEPENDENT_REVIEW",
            "work_packages": "0_OF_10_EXECUTED",
            "execution_controls": "0_OF_15_EXECUTED",
            "deterministic_vectors": 0,
            "gaussian_noise": "NONE",
            "monte_carlo": "NONE",
            "stage_b": "DEFERRED_NOT_AUTHORIZED",
            "alpha": "NOT_SELECTED",
            "scalar_branch": "NOT_ADOPTED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
        "claim_ceiling": (
            "This packet freezes one deterministic internal torsion-balance "
            "forward-model validation contract. It executes no kernel, benchmark, "
            "mutation, convergence check, Jacobian, or output; uses no noise, "
            "covariance, Monte Carlo, profile likelihood, or evidence; produces no "
            "forecast or parameter bound; and adopts no scalar branch or theory."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_packet(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Freeze the deterministic Yukawa torsion-balance validation packet.")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    args = parser.parse_args()
    output = REPO_ROOT / REPORT_RELATIVE_PATH
    expected = artifact_bytes()
    current = output.read_bytes() if output.exists() else None
    if args.write:
        if current != expected:
            output.write_bytes(expected)
            print(f"wrote {REPORT_RELATIVE_PATH}")
        else:
            print("deterministic validation packet already current")
        return 0
    if current != expected:
        print("deterministic validation packet drift")
        return 1
    print("deterministic validation packet OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
