from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
PACKET_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_SYNTHETIC_FORWARD_MODEL_AND_"
    "SENSITIVITY_FORECAST_PACKET_20260718_v0.json"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_SYNTHETIC_FORWARD_MODEL_AND_"
    "SENSITIVITY_FORECAST_PACKET_REVIEW_20260718_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_SYNTHETIC_FORWARD_MODEL_AND_"
    "SENSITIVITY_FORECAST_PACKET_REVIEW_20260718_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_scalar_only_yukawa_synthetic_forward_model_and_"
    "sensitivity_forecast_packet_review_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ScalarOnlyYukawaSyntheticForwardModelAndSensitivityForecastPacketReviewV0.lean"
)

TARGET = (
    "review_scalar_only_yukawa_synthetic_forward_model_and_"
    "sensitivity_forecast_packet_v0_result"
)
VERDICT = "BLOCKED_SYNTHETIC_NOISE_OR_NUISANCE_CONTRACT"
SELECTED_NEXT_TARGET = (
    "select_post_scalar_only_yukawa_synthetic_forward_model_and_"
    "sensitivity_forecast_packet_review_scientific_response_v0"
)
SELECTED_NEXT_TARGET_KIND = (
    "SCIENTIFIC_RESPONSE_SELECTION_ONLY_NO_PACKET_REPAIR_OR_SYNTHETIC_EXECUTION"
)

PACKET_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_SYNTHETIC_FORWARD_MODEL_AND_SENSITIVITY_FORECAST_PACKET_20260718_v0.md":
        "e107573a49ab743b70bfe5b223507924fdf3bd4ffc0c92eaf65809ed6350f949",
    PACKET_RELATIVE_PATH:
        "7102ed5a41e95792ab6a0be3d6b1321f05b1246600871752128940b5d1110217",
    "formal/python/tools/scalar_only_yukawa_synthetic_forward_model_and_sensitivity_forecast_packet_v0.py":
        "b32361b5fce58848846278bb7494f05b50e1361424f89cc586bc3f9ad3988cda",
    "formal/python/tests/test_scalar_only_yukawa_synthetic_forward_model_and_sensitivity_forecast_packet_v0.py":
        "80c2f8e3da34560cab118e7f8a7e09de3a70f10f10fdad7134761df8d6f5c26f",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaSyntheticForwardModelAndSensitivityForecastPacketV0.lean":
        "90d1223135ec26153f62b21d1fe97927f01a0b7b119923d35110b4a4db15e6ab",
}

DIAGNOSTICS = (
    "HARMONIC_NORMALIZATION_PHASE_CONVENTION_INCOMPLETE",
    "PRODUCTION_BENCHMARK_ROUTING_AND_MUTATION_INCOMPLETE",
    "COVARIANCE_FACTORIZATION_FAILURE_POLICY_INCOMPLETE",
    "NUISANCE_TRUTH_BOUND_EFFECT_CONTRACT_INCOMPLETE",
    "EXACT_MULTIPLICATIVE_NUISANCE_DEGENERACY",
    "OPTIMIZER_PARALLELIZATION_RESOURCE_CAP_INCOMPLETE",
    "PHASE_SIGN_MUTATION_AND_IDENTIFIABILITY_CONTROLS_MISSING",
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_packet() -> dict[str, Any]:
    value = json.loads((REPO_ROOT / PACKET_RELATIVE_PATH).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError("synthetic packet must be a JSON object")
    return value


def _artifact_row(relative_path: str) -> dict[str, str]:
    return {"relative_path": relative_path, "sha256": _sha256(REPO_ROOT / relative_path)}


def _gate(gate_id: str, passed: bool, finding: str) -> dict[str, Any]:
    return {"gate_id": gate_id, "status": "PASS" if passed else "FAIL", "finding": finding}


def build_review() -> dict[str, Any]:
    for relative_path, expected_hash in PACKET_HASHES.items():
        if _sha256(REPO_ROOT / relative_path) != expected_hash:
            raise ValueError(f"synthetic packet custody drift: {relative_path}")

    packet = _load_packet()
    if packet.get("verdict") != (
        "PREPARED_SYNTHETIC_FORECAST_CONTRACT_READY_PENDING_INDEPENDENT_REVIEW"
    ):
        raise ValueError("synthetic packet is not pending independent review")
    if packet.get("selected_next_target") != TARGET:
        raise ValueError("synthetic packet did not rotate to this review")
    if packet.get("scope", {}).get("synthetic_execution_authorized") is not False:
        raise ValueError("packet improperly authorized synthetic execution")

    gates = [
        _gate("G1_EXACT_PACKET_AUTHORITY_AND_CUSTODY", True, "Five packet artifacts match frozen SHA-256 values."),
        _gate("G2_SYNTHETIC_ONLY_STATUS_AND_SCOPE", True, "No measured evidence, Eot-Wash reproduction, empirical constraint, or branch adoption is claimed."),
        _gate("G3_FIXED_AMPLITUDE_MODEL_AND_SI_MAP", True, "A_Y=1/3 and the lambda0, m0, alpha maps are exact and no parameter is selected."),
        _gate("G4_IDEALIZED_GEOMETRY_DIMENSIONS_COMPLETE", True, "Sphere counts, radii, density, arm radii, gap grid, centers, and gap definition are frozen."),
        _gate("G5_GEOMETRY_GENERATES_DECLARED_EVEN_HARMONICS", True, "Analytic symmetry and a representative dimensionless calculation show nonzero n=2,4,6 sine harmonics."),
        _gate("G6_REAL_OBSERVATION_COUNT_REPRODUCED", True, "25 gaps x 3 harmonics x 2 real quadratures equals a real 150-vector."),
        _gate("G7_EXACT_HARMONIC_NORMALIZATION_AND_PHASE", False, "DFT sign, normalization, phase origin, alias handling, and torque derivative convention are not frozen."),
        _gate("G8_PRODUCTION_KERNEL_BENCHMARK_ROUTING", False, "Production pair kernel, derivative, cubature sequence, and deliberate mutation tests are incomplete."),
        _gate("G9_COVARIANCE_MATHEMATICALLY_SPD", True, "The real 150x150 Kronecker covariance is symmetric positive definite with moderate condition number."),
        _gate("G10_COVARIANCE_NUMERICAL_FAILURE_POLICY", False, "Factorization, threshold, jitter/clipping prohibition or rule, and fail-closed behavior are absent."),
        _gate("G11_RANGE_GRID_COVERS_THREE_REGIMES", True, "The finite logarithmic grid spans lambda below, within, and above the gap domain."),
        _gate("G12_MONTE_CARLO_RESOLUTION_MATCHES_ORDINARY_FORECAST", True, "Trial counts resolve ordinary 95-percent power and coverage with reported binomial uncertainty, not five sigma."),
        _gate("G13_NUISANCE_TRUTHS_BOUNDS_AND_EXACT_EFFECTS", False, "All truth values, bounds, leakage/background maps, and invalid-domain behavior are not frozen."),
        _gate("G14_NUISANCE_DATA_IDENTIFIABILITY", False, "Calibration and density/mass scale have identical nominal data-Jacobian columns."),
        _gate("G15_BOUNDARY_CALIBRATION_FAILS_CLOSED", True, "Null thresholds and pointwise coverage are simulation calibrated; Wilks is prohibited."),
        _gate("G16_COMPUTATIONAL_EXECUTION_PLAN", False, "Optimizer, derivatives, starts, limits, retries, parallelization, resources, and failed-fit handling are missing."),
        _gate("G17_ADVERSARIAL_PHASE_SIGN_MUTATION_AND_RANK_CONTROLS", False, "Required sign-reversal, deliberate-mutation, nuisance-monotonicity, and rank controls are absent."),
        _gate("G18_NUMERICAL_CONVERGENCE_THRESHOLDS", True, "Angular, transport, cubature, and design-refinement tolerances are bounded and fail closed."),
        _gate("G19_FORECAST_OUTPUT_PRECISION_CEILING", True, "Eight output classes and Monte Carlo uncertainty prevent excess precision claims."),
        _gate("G20_NO_SYNTHETIC_EXECUTION_DURING_REVIEW", True, "No dataset, trial, profile fit, or forecast output was produced."),
        _gate("G21_STANDING_NO_CONTACT_AND_PUBLIC_ONLY_POLICY", True, "The internal-only public-information scope remains binding."),
        _gate("G22_NO_EMPIRICAL_OR_THEORY_PROMOTION", True, "No bound, scalar adoption, native bridge, action selection, or downstream GR claim occurs."),
    ]
    pass_count = sum(row["status"] == "PASS" for row in gates)

    unblock_text = [
        "freeze real-150 harmonic normalization phase sign and alias conventions",
        "freeze shared production kernel torque derivative cubature refinement and mutation gates",
        "freeze covariance factorization conditioning and regularization failure policy",
        "freeze all nuisance truth values bounds exact effects and invalid-domain behavior",
        "combine or physically distinguish the exact multiplicative nuisance pair and require rank diagnostics",
        "freeze optimizer derivatives starts warm starts limits retries parallel resources checkpoints and failed-fit handling",
        "add phase-sign reversal deliberate mutation nuisance-removal monotonicity and identifiability controls",
    ]

    scope = {
        "independent_packet_review_executed": True,
        "geometry_even_harmonics_verified": True,
        "real_150_observation_count_verified": True,
        "covariance_mathematical_positive_definiteness_verified": True,
        "nuisance_degeneracy_identified": True,
        "packet_execution_ready": False,
        "packet_repair_authorized": False,
        "synthetic_execution_authorized": False,
        "synthetic_execution_performed": False,
        "synthetic_dataset_generated": False,
        "forecast_output_produced": False,
        "measured_evidence_used": False,
        "eotwash_reproduction_claimed": False,
        "empirical_constraint_claimed": False,
        "outbound_contact_authorized": False,
        "private_data_dependency_created": False,
        "numerical_lambda_bound_computed": False,
        "numerical_alpha_bound_computed": False,
        "alpha_sign_or_value_adopted": False,
        "scalar_branch_adopted": False,
        "native_scalar_bridge_identified": False,
        "native_gravitational_principle_identified": False,
        "gravitational_action_selected": False,
        "frame_dragging_resumed": False,
        "master_action_mutated": False,
    }

    return {
        "schema_id": "toe.scalar_only_yukawa.synthetic_forward_model_and_sensitivity_forecast.packet_review.v0",
        "packet_id": "SCALAR_ONLY_YUKAWA_SYNTHETIC_FORWARD_MODEL_AND_SENSITIVITY_FORECAST_PACKET_REVIEW_20260718_v0",
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "principal_packet_review_outcome": VERDICT,
        "execution_readiness": "NOT_READY",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_packet_verdict": packet["verdict"],
            "frozen_packet_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in PACKET_HASHES.items()
            ],
            "human_review": _artifact_row(HUMAN_RELATIVE_PATH),
            "generator": _artifact_row(
                "formal/python/tools/scalar_only_yukawa_synthetic_forward_model_"
                "and_sensitivity_forecast_packet_review_v0.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
        },
        "independent_geometry_check": {
            "pair_distance_minus_squared": "z^2+2*L^2*(1-cos(theta))",
            "pair_distance_plus_squared": "z^2+2*L^2*(1+cos(theta))",
            "energy_pair_structure": "2*(u(r_minus)+u(r_plus))",
            "energy_pi_periodic": True,
            "torque_odd": True,
            "only_even_sine_harmonics_nominal": True,
            "n2_n4_n6_nonzero_representative_check": True,
            "representative_symmetry_residual_max": 8.7e-13,
            "forecast_output_produced": False,
        },
        "observation_convention_review": {
            "gap_count": 25,
            "harmonic_count": 3,
            "real_quadrature_count": 2,
            "real_observation_count": 150,
            "complex_observation_count_claim": False,
            "real_covariance_dimension": 150,
            "exact_dft_normalization_complete": False,
        },
        "covariance_review": {
            "interpretation": "R_gap_KRONECKER_DIAG_CHANNEL_VARIANCES",
            "real_covariance_dimension": 150,
            "symmetric_positive_definite": True,
            "minimum_gap_correlation_eigenvalue": 0.1733442158,
            "gap_correlation_condition_number": 30.7757013,
            "full_covariance_condition_number": 69.2453279,
            "maximum_symmetry_residual_si": 2.6e-49,
            "factorization_and_failure_policy_complete": False,
        },
        "monte_carlo_review": {
            "null_trials": 2000,
            "injection_trials_per_positive_lambda": 1000,
            "positive_lambda_count": 25,
            "injection_trials": 25000,
            "zero_noise_trials": 26,
            "total_synthetic_datasets_if_authorized": 27026,
            "maximum_injection_binomial_standard_error": 0.0158113883,
            "smallest_direct_null_tail_probability": 1 / 2001,
            "ordinary_95_percent_forecast_supported": True,
            "five_sigma_calibration_supported": False,
        },
        "nuisance_identifiability_review": {
            "declared_nuisance_count": 11,
            "data_jacobian_degeneracy": (
                "TORQUE_CALIBRATION_COLUMN_EQUALS_DENSITY_MASS_SCALE_COLUMN_"
                "AT_NOMINAL_POINT"
            ),
            "separately_data_identifiable": False,
            "penalized_fit_finite_due_to_priors": True,
            "truth_values_bounds_and_maps_complete": False,
            "contract_complete": False,
        },
        "computational_execution_plan_review": {
            "synthetic_dataset_count": 27026,
            "candidate_range_count": 25,
            "minimum_outer_profile_fit_count": 675000,
            "complete": False,
            "missing_items": [
                "OPTIMIZER",
                "DERIVATIVE_METHOD",
                "INITIAL_CONDITIONS",
                "WARM_START_POLICY",
                "MAXIMUM_ITERATIONS_AND_EVALUATIONS",
                "FIT_CONVERGENCE_TOLERANCE",
                "RETRY_POLICY",
                "PARALLELIZATION",
                "RANDOM_STREAM_TO_WORKER_PARTITION",
                "FAILED_FIT_CLASSIFICATION",
                "WALL_TIME_AND_MEMORY_CAP",
                "CHECKPOINT_AND_RESUME_POLICY",
            ],
        },
        "diagnostics": list(DIAGNOSTICS),
        "unblock_requirements": [
            {"requirement_id": f"U{index}", "requirement": text, "satisfied": False}
            for index, text in enumerate(unblock_text, start=1)
        ],
        "review_gates": {
            "gate_count": len(gates),
            "pass_count": pass_count,
            "failure_count": len(gates) - pass_count,
            "rows": gates,
        },
        "scope": scope,
        "current_posture": {
            "packet_review": "COMPLETED",
            "principal_outcome": VERDICT,
            "synthetic_execution": "NOT_AUTHORIZED",
            "work_packages": "0_OF_8_EXECUTED",
            "synthetic_observations": 0,
            "null_trials": "0_OF_2000",
            "injection_trials": "0_OF_25000",
            "forecast_outputs": "0_OF_8",
            "empirical_constraint": "NONE",
            "alpha": "NOT_SELECTED",
            "scalar_branch": "NOT_ADOPTED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
        "claim_ceiling": (
            "The review verifies the geometry's even harmonics, the real-150 "
            "observation count, covariance positive definiteness, bounded range "
            "grid, and Monte Carlo resolution, while blocking execution on seven "
            "underdefined forward-model, covariance, nuisance, optimizer, and "
            "control interfaces. It authorizes no repair, simulation, forecast, "
            "empirical claim, parameter bound, or theory adoption."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_review(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Review the scalar-only Yukawa synthetic forecast packet.")
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
            print("synthetic forecast packet review already current")
        return 0
    if current != expected:
        print("synthetic forecast packet review drift")
        return 1
    print("synthetic forecast packet review OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

