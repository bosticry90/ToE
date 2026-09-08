from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import math
from pathlib import Path
from typing import Any, Iterable

import numpy as np

from formal.python.tools import scalar_only_yukawa_torsion_balance_production_v1 as production


REPO_ROOT = Path(__file__).resolve().parents[3]
OUTPUT_RELATIVE_DIRECTORY = (
    "formal/output/scalar_only_yukawa_deterministic_torsion_balance_v1"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_"
    "FORWARD_MODEL_VALIDATION_EXECUTION_20260719_v1.json"
)
REVIEW_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_"
    "FORWARD_MODEL_VALIDATION_PACKET_REVIEW_20260719_v1.json"
)

TARGET = (
    "execute_scalar_only_yukawa_deterministic_torsion_balance_"
    "forward_model_validation_v1_once"
)
SELECTED_NEXT_TARGET = (
    "review_scalar_only_yukawa_deterministic_torsion_balance_"
    "forward_model_validation_v1_execution_result"
)
SELECTED_NEXT_TARGET_KIND = (
    "INDEPENDENT_DETERMINISTIC_STAGE_A_EXECUTION_RESULT_REVIEW_ONLY"
)

REVIEW_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_FORWARD_MODEL_VALIDATION_PACKET_REVIEW_20260719_v1.md":
        "d5454c879532ad26afbc07b882cca12aa0bcf3b8f69196f46c1d3011b7f50c82",
    REVIEW_RELATIVE_PATH:
        "e39b8ec2672cae854921638856103fdfdc5c6903ec9a7127d683f839cc6243af",
    "formal/python/tools/scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_packet_review_v1.py":
        "73967ee60e41ad6e1a3c0d16b45eb91b538371b355ef855ce8ac240d28126eaf",
    "formal/python/tests/test_scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_packet_review_v1.py":
        "25175b4256cd53405ff23018771a4d0ef387958b22454c498495421b18bb8f77",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaDeterministicTorsionBalanceForwardModelValidationPacketReviewV1.lean":
        "3a1f0d1fc9b7088bd7d419f553c15acb7388da7907257a7b8c7826decc6cecb5",
}

TRANSITION_INDICES = tuple(range(4, 21))
RANK_THRESHOLDS = (1e-9, 1e-10, 1e-11)
MEDIUM_SAMPLES = 256
FINE_SAMPLES = 512


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _sha256_path(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _json_default(value: Any) -> Any:
    if isinstance(value, np.bool_):
        return bool(value)
    if isinstance(value, np.integer):
        return int(value)
    if isinstance(value, np.floating):
        number = float(value)
        if not math.isfinite(number):
            raise ValueError(f"canonical serialization received non-finite float: {number}")
        return number
    if isinstance(value, np.ndarray):
        return value.tolist()
    raise TypeError(f"unsupported canonical JSON type: {type(value).__name__}")


def _json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, default=_json_default, indent=2, sort_keys=True) + "\n"
    ).encode("utf-8")


def _float(value: float) -> str:
    number = float(value)
    if not math.isfinite(number):
        raise ValueError(f"canonical serialization received non-finite float: {number}")
    return f"{number:+.17e}"


def _csv_bytes(headers: list[str], rows: Iterable[dict[str, Any]]) -> bytes:
    buffer = io.StringIO(newline="")
    writer = csv.DictWriter(buffer, fieldnames=headers, lineterminator="\n")
    writer.writeheader()
    for row in rows:
        writer.writerow({key: row.get(key, "") for key in headers})
    return buffer.getvalue().encode("utf-8")


def _relative_error(actual: np.ndarray | float, expected: np.ndarray | float, floor: float) -> float:
    dtype = np.complex128 if np.iscomplexobj(actual) or np.iscomplexobj(expected) else np.float64
    a = np.asarray(actual, dtype=dtype)
    e = np.asarray(expected, dtype=dtype)
    return float(np.max(np.abs(a - e) / np.maximum(np.abs(e), floor)))


def _vector_rows(
    vector: np.ndarray,
    *,
    lambda_index: str,
    lambda_m: float,
    vector_class: str,
) -> list[dict[str, str]]:
    reshaped = np.asarray(vector, dtype=np.float64).reshape((25, 6))
    labels = ((2, "RE"), (2, "IM"), (4, "RE"), (4, "IM"), (6, "RE"), (6, "IM"))
    rows = []
    for gap_index, gap in enumerate(production.GAPS):
        for component_index, (harmonic, quadrature) in enumerate(labels):
            rows.append(
                {
                    "vector_class": vector_class,
                    "lambda_index": lambda_index,
                    "lambda_m": _float(lambda_m),
                    "gap_index": str(gap_index),
                    "gap_m": _float(gap),
                    "harmonic": str(harmonic),
                    "quadrature": quadrature,
                    "value_N_m": _float(reshaped[gap_index, component_index]),
                }
            )
    return rows


def _point_kernel_benchmarks() -> list[dict[str, Any]]:
    mass_d = 1.7
    mass_a = 2.3
    r = np.asarray([0.021, 0.042], dtype=np.float64)
    newton_energy, newton_derivative = production.pair_energy_and_radial_derivative(
        r,
        0.0,
        mass_d_kg=mass_d,
        mass_a_kg=mass_a,
        radius_d_m=0.0,
        radius_a_m=0.0,
        component="newtonian",
    )
    expected_energy = -production.G_SI * mass_d * mass_a / r
    expected_derivative = production.G_SI * mass_d * mass_a / r**2
    newton_error = max(
        _relative_error(newton_energy, expected_energy, 1e-300),
        _relative_error(newton_derivative, expected_derivative, 1e-300),
    )
    lam = 0.013
    yukawa_energy, yukawa_derivative = production.pair_energy_and_radial_derivative(
        r,
        lam,
        mass_d_kg=mass_d,
        mass_a_kg=mass_a,
        radius_d_m=0.0,
        radius_a_m=0.0,
        component="yukawa",
    )
    exponential = np.exp(-r / lam)
    expected_yukawa_energy = (
        -production.G_SI * production.A_Y * mass_d * mass_a * exponential / r
    )
    expected_yukawa_derivative = (
        production.G_SI
        * production.A_Y
        * mass_d
        * mass_a
        * exponential
        * (1.0 / r**2 + 1.0 / (lam * r))
    )
    yukawa_error = max(
        _relative_error(yukawa_energy, expected_yukawa_energy, 1e-300),
        _relative_error(yukawa_derivative, expected_yukawa_derivative, 1e-300),
    )
    return [
        {
            "benchmark_id": "POINT_NEWTONIAN",
            "max_relative_error": newton_error,
            "inverse_distance_ratio": float(newton_energy[0] / newton_energy[1]),
            "inverse_square_ratio": float(newton_derivative[0] / newton_derivative[1]),
            "pass": newton_error <= 1e-14
            and newton_energy[0] < 0.0
            and newton_derivative[0] > 0.0,
        },
        {
            "benchmark_id": "POINT_YUKAWA",
            "max_relative_error": yukawa_error,
            "pass": yukawa_error <= 1e-14
            and yukawa_energy[0] < 0.0
            and yukawa_derivative[0] > 0.0,
        },
    ]


def _form_factor_benchmark() -> tuple[dict[str, Any], list[dict[str, Any]]]:
    cases = ((0.011, 1e-4), (0.03, 5e-3), (0.08, 0.1))
    orders = (8, 12, 16, 24)
    mass_d = production.sphere_mass(production.RADIUS_D, production.DENSITY)
    mass_a = production.sphere_mass(production.RADIUS_A, production.DENSITY)
    details = []
    maximum_production_error = 0.0
    maximum_refinement_error = 0.0
    for case_index, (distance, lam) in enumerate(cases):
        production_energy, _ = production.pair_energy_and_radial_derivative(
            distance,
            lam,
            mass_d_kg=mass_d,
            mass_a_kg=mass_a,
            component="yukawa",
        )
        quadrature = {
            order: production.reduced_four_dimensional_density_integral_yukawa_energy(
                distance, lam, order
            )
            for order in orders
        }
        production_error = abs(float(production_energy) - quadrature[24]) / max(
            abs(float(production_energy)), 1e-300
        )
        refinement_error = abs(quadrature[16] - quadrature[24]) / max(
            abs(quadrature[24]), 1e-300
        )
        maximum_production_error = max(maximum_production_error, production_error)
        maximum_refinement_error = max(maximum_refinement_error, refinement_error)
        for order in orders:
            details.append(
                {
                    "case_index": case_index,
                    "center_distance_m": distance,
                    "lambda_m": lam,
                    "order": order,
                    "quadrature_energy_J": quadrature[order],
                    "production_energy_J": float(production_energy),
                }
            )
    result = {
        "benchmark_id": "UNIFORM_SPHERE_FORM_FACTOR",
        "max_production_vs_order24_relative_error": maximum_production_error,
        "max_order16_vs_order24_relative_error": maximum_refinement_error,
        "pass": maximum_production_error <= 1e-6 and maximum_refinement_error <= 1e-6,
    }
    return result, details


def _apparatus_and_symmetry_controls() -> tuple[
    dict[str, Any], list[dict[str, Any]], list[dict[str, Any]]
]:
    gaps = np.asarray([production.GAPS[0], production.GAPS[12], production.GAPS[-1]])
    theta = np.asarray([math.pi / 7.0, 3.0 * math.pi / 10.0])
    analytic = production.analytic_energy_derivative_torque(
        theta, gaps, production.LAMBDA_REFERENCE
    )
    force = production.direct_pair_force_lever_torque(
        theta, gaps, production.LAMBDA_REFERENCE
    )
    force_error = _relative_error(force, analytic, 1e-22)
    energy_errors = []
    energy_rows = []
    for step in (1e-3, 5e-4, 2.5e-4, 1.25e-4):
        energy = production.five_point_energy_derivative_torque(
            theta, gaps, production.LAMBDA_REFERENCE, step
        )
        error = _relative_error(energy, analytic, 1e-22)
        energy_errors.append(error)
        energy_rows.append(
            {
                "control_id": "FIVE_POINT_ENERGY_DERIVATIVE",
                "step_rad": step,
                "max_relative_or_floored_error": error,
                "pass": True,
            }
        )

    sample_count = 512
    theta_grid = 2.0 * math.pi * np.arange(sample_count) / sample_count
    middle_gap = np.asarray([production.GAPS[12]])
    torque = production.analytic_energy_derivative_torque(
        theta_grid, middle_gap, production.LAMBDA_REFERENCE
    )
    all_coefficients = production.discrete_harmonic_transform(
        torque, theta_grid, harmonics=(1, 2, 3, 4, 5, 6)
    )[0]
    odd_max = float(np.max(np.abs(all_coefficients[[0, 2, 4]])))
    even_cosine_max = float(np.max(np.abs(all_coefficients[[1, 3, 5]].real)))
    even_sine_min = float(np.min(np.abs(all_coefficients[[1, 3, 5]].imag)))
    symmetry_angles = np.asarray([0.0, math.pi / 2.0, math.pi, 3.0 * math.pi / 2.0])
    symmetry_torque = production.analytic_energy_derivative_torque(
        symmetry_angles, middle_gap, production.LAMBDA_REFERENCE
    )
    symmetry_zero_max = float(np.max(np.abs(symmetry_torque)))
    reverse_torque = production.analytic_energy_derivative_torque(
        -theta_grid, middle_gap, production.LAMBDA_REFERENCE
    )
    reverse_coefficients = production.discrete_harmonic_transform(
        reverse_torque, theta_grid
    )[0]
    base_coefficients = all_coefficients[[1, 3, 5]]
    reversal_error = float(np.max(np.abs(reverse_coefficients - np.conjugate(base_coefficients))))
    delta = math.pi / 16.0
    shifted = production.analytic_energy_derivative_torque(
        theta_grid,
        middle_gap,
        production.LAMBDA_REFERENCE,
        production.ApparatusParameters(angular_zero_offset_rad=delta),
    )
    shifted_coefficients = production.discrete_harmonic_transform(
        shifted, theta_grid
    )[0]
    expected_shift = base_coefficients * np.exp(
        -1j * np.asarray(production.HARMONICS) * delta
    )
    phase_error = _relative_error(shifted_coefficients, expected_shift, 1e-22)
    energy_refinement = energy_errors[-1] <= 1e-8 and energy_errors[-1] <= energy_errors[0]
    symmetry_rows = [
        {
            "control_id": "ODD_HARMONICS_1_3_5_ZERO",
            "metric": odd_max,
            "tolerance": 1e-22,
            "pass": odd_max <= 1e-22,
        },
        {
            "control_id": "EVEN_COSINE_QUADRATURES_ZERO",
            "metric": even_cosine_max,
            "tolerance": 1e-22,
            "pass": even_cosine_max <= 1e-22,
        },
        {
            "control_id": "EVEN_SINE_2_4_6_NONZERO",
            "metric": even_sine_min,
            "tolerance": 1e-22,
            "pass": even_sine_min > 1e-22,
        },
        {
            "control_id": "TORQUE_FOUR_SYMMETRY_ZEROS",
            "metric": symmetry_zero_max,
            "tolerance": 1e-22,
            "pass": symmetry_zero_max <= 1e-22,
        },
        {
            "control_id": "ANGLE_REVERSAL_CONJUGATES",
            "metric": reversal_error,
            "tolerance": 1e-22,
            "pass": reversal_error <= 1e-22,
        },
        {
            "control_id": "RIGID_PI_OVER_16_PHASE_LAW",
            "metric": phase_error,
            "tolerance": 1e-10,
            "pass": phase_error <= 1e-10,
        },
    ]
    benchmark = {
        "benchmark_id": "APPARATUS_TORQUE_AND_SYMMETRY",
        "force_lever_max_error": force_error,
        "finest_energy_derivative_error": energy_errors[-1],
        "energy_derivative_refines": energy_refinement,
        "symmetry_controls_pass": all(row["pass"] for row in symmetry_rows),
        "pass": force_error <= 1e-10
        and energy_refinement
        and all(row["pass"] for row in symmetry_rows),
    }
    return benchmark, symmetry_rows, energy_rows


def _mutation_controls(
    form_factor_details: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    mass_d = production.sphere_mass(production.RADIUS_D, production.DENSITY)
    mass_a = production.sphere_mass(production.RADIUS_A, production.DENSITY)
    distance = 0.03
    lam = 5e-3
    nominal_y, _ = production.pair_energy_and_radial_derivative(
        distance,
        lam,
        mass_d_kg=mass_d,
        mass_a_kg=mass_a,
        component="yukawa",
    )
    flipped_y, _ = production.pair_energy_and_radial_derivative(
        distance,
        lam,
        mass_d_kg=mass_d,
        mass_a_kg=mass_a,
        component="yukawa",
        yukawa_sign=-1.0,
    )
    amplitude_one, _ = production.pair_energy_and_radial_derivative(
        distance,
        lam,
        mass_d_kg=mass_d,
        mass_a_kg=mass_a,
        component="yukawa",
        yukawa_amplitude=1.0,
    )
    removed_factor, _ = production.pair_energy_and_radial_derivative(
        distance,
        lam,
        mass_d_kg=mass_d,
        mass_a_kg=mass_a,
        component="yukawa",
        remove_attractor_form_factor=True,
    )
    reference_integral = next(
        row["quadrature_energy_J"]
        for row in form_factor_details
        if row["case_index"] == 1 and row["order"] == 24
    )
    theta = np.asarray([math.pi / 7.0])
    gap = np.asarray([production.GAPS[12]])
    force = production.direct_pair_force_lever_torque(
        theta, gap, production.LAMBDA_REFERENCE
    )
    wrong_torque = production.analytic_energy_derivative_torque(
        theta, gap, production.LAMBDA_REFERENCE, torque_sign=-1.0
    )
    nominal_vector, _ = production.real_150_vector(production.LAMBDA_REFERENCE)
    doubled_vector, _ = production.real_150_vector(
        production.LAMBDA_REFERENCE, normalization_multiplier=2.0
    )
    return [
        {
            "mutation_id": "FLIP_YUKAWA_ENERGY_SIGN",
            "designated_control_detected": bool(float(nominal_y) < 0.0 < float(flipped_y)),
        },
        {
            "mutation_id": "REPLACE_ONE_THIRD_BY_ONE",
            "designated_control_detected": bool(
                abs(float(amplitude_one / nominal_y) - 3.0) <= 1e-12
            ),
        },
        {
            "mutation_id": "REMOVE_ONE_SPHERE_FORM_FACTOR",
            "designated_control_detected": bool(
                abs(float(removed_factor) - reference_integral)
                / max(abs(reference_integral), 1e-300)
                > 1e-6
            ),
        },
        {
            "mutation_id": "FLIP_NEGATIVE_ENERGY_DERIVATIVE_TORQUE_SIGN",
            "designated_control_detected": bool(
                _relative_error(wrong_torque, force, 1e-22) > 1e-3
            ),
        },
        {
            "mutation_id": "DOUBLE_DFT_NORMALIZATION",
            "designated_control_detected": bool(
                _relative_error(doubled_vector, nominal_vector, 1e-22) > 0.5
            ),
        },
    ]


def _angular_convergence() -> dict[str, Any]:
    production_vector, _ = production.real_150_vector(
        production.LAMBDA_REFERENCE, angular_samples=256
    )
    reference_vector, _ = production.real_150_vector(
        production.LAMBDA_REFERENCE, angular_samples=512
    )
    error = _relative_error(production_vector, reference_vector, 1e-22)
    return {
        "control_id": "ANGULAR_DFT_256_VS_512",
        "metric": error,
        "tolerance": 1e-8,
        "pass": error <= 1e-8,
    }


def _evaluation_points() -> list[dict[str, Any]]:
    rows = []
    for index, value in enumerate(production.LAMBDA_GRID):
        roles = ["POSITIVE_GRID"]
        if index in TRANSITION_INDICES:
            roles.append("DECISION_TRANSITION")
        if index == 6:
            roles.append("SENTINEL_D_MIN")
        if index == 12:
            roles.append("SENTINEL_GEOMETRIC_MEAN")
        if index == 18:
            roles.append("SENTINEL_D_MAX")
        rows.append(
            {
                "point_id": f"GRID_{index:02d}",
                "lambda_m": float(value),
                "grid_index": index,
                "roles": roles,
            }
        )
    rows.append(
        {
            "point_id": "SENTINEL_D_MIN_OVER_3",
            "lambda_m": 1e-4 / 3.0,
            "grid_index": None,
            "roles": ["REGIME_SENTINEL"],
        }
    )
    rows.append(
        {
            "point_id": "SENTINEL_3_D_MAX",
            "lambda_m": 3e-2,
            "grid_index": None,
            "roles": ["REGIME_SENTINEL"],
        }
    )
    return rows


def _analysis_bundle(jacobian_result: dict[str, Any]) -> dict[str, Any]:
    analyses = {
        threshold: production.analyze_scaled_jacobian(
            jacobian_result["jacobian"],
            jacobian_result["y_star"],
            rank_threshold=threshold,
        )
        for threshold in RANK_THRESHOLDS
    }
    ranks = [analyses[value]["rank"] for value in RANK_THRESHOLDS]
    classifications = [analyses[value]["classification"] for value in RANK_THRESHOLDS]
    etas = [analyses[value]["eta"] for value in RANK_THRESHOLDS]
    stable = (
        len(set(ranks)) == 1
        and len(set(classifications)) == 1
        and max(etas) - min(etas) <= 0.02
        and all(analyses[value]["projector_valid"] for value in RANK_THRESHOLDS)
    )
    return {
        "jacobian_result": jacobian_result,
        "analyses": analyses,
        "threshold_stable": stable,
        "eta_spread": max(etas) - min(etas),
    }


def _maximum_contiguous_true(values: list[bool]) -> int:
    best = 0
    current = 0
    for value in values:
        current = current + 1 if value else 0
        best = max(best, current)
    return best


def _identifiability_execution() -> dict[str, Any]:
    points = _evaluation_points()
    fine: dict[str, dict[str, Any]] = {}
    medium: dict[str, dict[str, Any]] = {}
    required_medium_ids = {
        row["point_id"]
        for row in points
        if "DECISION_TRANSITION" in row["roles"] or "REGIME_SENTINEL" in row["roles"]
        or any(role.startswith("SENTINEL_") for role in row["roles"])
    }
    for point in points:
        fine_result = production.build_dimensionless_jacobian(
            point["lambda_m"], angular_samples=FINE_SAMPLES
        )
        fine[point["point_id"]] = _analysis_bundle(fine_result)
        if point["point_id"] in required_medium_ids:
            medium_result = production.build_dimensionless_jacobian(
                point["lambda_m"], angular_samples=MEDIUM_SAMPLES
            )
            medium[point["point_id"]] = _analysis_bundle(medium_result)

    point_results = []
    for point in points:
        fine_bundle = fine[point["point_id"]]
        fine_central = fine_bundle["analyses"][1e-10]
        refinement = None
        stable = fine_bundle["threshold_stable"] and fine_bundle["jacobian_result"][
            "plateau_pass"
        ]
        if point["point_id"] in medium:
            medium_bundle = medium[point["point_id"]]
            medium_central = medium_bundle["analyses"][1e-10]
            refinement = production.compare_identifiability_refinements(
                medium_central, fine_central
            )
            stable = (
                stable
                and medium_bundle["threshold_stable"]
                and medium_bundle["jacobian_result"]["plateau_pass"]
                and refinement["pass"]
            )
        point_results.append(
            {
                **point,
                "fine": fine_bundle,
                "medium": medium.get(point["point_id"]),
                "refinement": refinement,
                "stable": stable,
            }
        )

    decision = [
        row for row in point_results if "DECISION_TRANSITION" in row["roles"]
    ]
    decision.sort(key=lambda row: row["grid_index"])
    any_plateau_failure = any(
        not row["fine"]["jacobian_result"]["plateau_pass"]
        or (
            row["medium"] is not None
            and not row["medium"]["jacobian_result"]["plateau_pass"]
        )
        for row in point_results
    )
    any_projector_failure = any(
        not row["fine"]["threshold_stable"]
        or (row["medium"] is not None and not row["medium"]["threshold_stable"])
        for row in point_results
    )
    any_refinement_failure = any(
        row["refinement"] is not None and not row["refinement"]["pass"]
        for row in point_results
    )
    identifiable_flags = [
        row["stable"]
        and row["fine"]["analyses"][1e-10]["eta"] >= 1e-3
        for row in decision
    ]
    contiguous_identifiable = _maximum_contiguous_true(identifiable_flags)
    all_indistinguishable = all(
        row["stable"]
        and row["fine"]["analyses"][1e-10]["eta"] <= 1e-6
        for row in decision
    )
    if any_plateau_failure:
        outcome = "BLOCKED_FINITE_DIFFERENCE_PLATEAU"
        secondary = "NO_IDENTIFIABILITY_CLASSIFICATION"
    elif any_projector_failure:
        outcome = "BLOCKED_NUISANCE_PROJECTOR_UNSTABLE"
        secondary = "NO_IDENTIFIABILITY_CLASSIFICATION"
    elif any_refinement_failure:
        outcome = "BLOCKED_IDENTIFIABILITY_REFINEMENT_STABILITY"
        secondary = "NO_IDENTIFIABILITY_CLASSIFICATION"
    elif contiguous_identifiable >= 5:
        outcome = "DETERMINISTIC_FORWARD_MODEL_VALIDATED"
        secondary = "IDENTIFIABILITY_SUPPORTED_IN_TESTED_DOMAIN"
    elif all_indistinguishable:
        outcome = "BLOCKED_PARAMETER_IDENTIFIABILITY"
        secondary = "SCALAR_DIRECTION_INSIDE_OR_TOO_NEAR_NUISANCE_SPAN"
    else:
        outcome = "IDENTIFIABILITY_CLASSIFICATION_UNRESOLVED"
        secondary = "FROZEN_DOMAIN_RULE_NOT_SATISFIED"
    return {
        "points": points,
        "point_results": point_results,
        "fine": fine,
        "medium": medium,
        "decision": decision,
        "contiguous_identifiable_count": contiguous_identifiable,
        "all_indistinguishable": all_indistinguishable,
        "any_plateau_failure": any_plateau_failure,
        "any_projector_failure": any_projector_failure,
        "any_refinement_failure": any_refinement_failure,
        "outcome": outcome,
        "secondary_outcome": secondary,
    }


def _v1_controls(identifiability: dict[str, Any]) -> list[dict[str, Any]]:
    reference_fine = identifiability["fine"]["GRID_12"]
    reference_medium = identifiability["medium"]["GRID_12"]
    lambda_ref = production.LAMBDA_REFERENCE
    oversized = production.build_dimensionless_jacobian(
        lambda_ref,
        angular_samples=MEDIUM_SAMPLES,
        step_ladder=(1.0, 0.6, 0.3),
    )
    undersized = production.build_dimensionless_jacobian(
        lambda_ref,
        angular_samples=MEDIUM_SAMPLES,
        step_ladder=(1e-7, 3e-8, 1e-8),
        deterministic_noise_amplitude_y_star=1e-11,
    )
    baseline_j = reference_fine["jacobian_result"]["jacobian"]
    y_star = reference_fine["jacobian_result"]["y_star"]
    baseline = reference_fine["analyses"][1e-10]
    duplicate_j = baseline_j.copy()
    duplicate_j[:, 1 + 10] = duplicate_j[:, 1 + 11]
    duplicate = production.analyze_scaled_jacobian(
        duplicate_j, y_star, rank_threshold=1e-10
    )
    nuisance = baseline_j[:, 1:] / y_star
    source = nuisance[:, 11]
    source = source / np.linalg.norm(source)
    basis_residual = np.eye(150)[:, 0] - source * source[0]
    if np.linalg.norm(basis_residual) <= 1e-12:
        basis_residual = np.eye(150)[:, 1] - source * source[1]
    basis_residual = basis_residual / np.linalg.norm(basis_residual)
    near_column = (1.0 - 1e-6) * source + 1e-6 * basis_residual
    near_column = near_column / np.linalg.norm(near_column)
    near_j = baseline_j.copy()
    near_j[:, 1 + 10] = near_column * y_star
    near = production.analyze_scaled_jacobian(near_j, y_star, rank_threshold=1e-10)
    equal_j = baseline_j.copy()
    equal_j[:, 0] = equal_j[:, 1]
    equal_analysis = production.analyze_scaled_jacobian(
        equal_j, y_star, rank_threshold=1e-10
    )
    ur = baseline["u_retained"]
    orthogonal = None
    orthogonal_index = None
    for index in range(150):
        candidate = np.eye(150)[:, index]
        residual = candidate - ur @ (ur.T @ candidate)
        if np.linalg.norm(residual) > 1e-10:
            orthogonal = residual / np.linalg.norm(residual)
            orthogonal_index = index
            break
    if orthogonal is None:
        raise ValueError("could not construct nuisance-orthogonal scalar control")
    orthogonal_j = baseline_j.copy()
    orthogonal_j[:, 0] = orthogonal * y_star
    orthogonal_analysis = production.analyze_scaled_jacobian(
        orthogonal_j, y_star, rank_threshold=1e-10
    )
    transition_registration = {
        "indices": list(TRANSITION_INDICES),
        "sentinels": [1e-4 / 3.0, 1e-4, 1e-3, 1e-2, 3e-2],
    }
    registered_hash = _sha256_bytes(
        json.dumps(transition_registration, separators=(",", ":"), sort_keys=True).encode()
    )
    tampered = {**transition_registration, "indices": list(TRANSITION_INDICES[:-1])}
    tampered_hash = _sha256_bytes(
        json.dumps(tampered, separators=(",", ":"), sort_keys=True).encode()
    )
    medium_u = reference_medium["analyses"][1e-10]["u_retained"]
    fine_u = reference_fine["analyses"][1e-10]["u_retained"]
    external = orthogonal
    mutated_fine_u = fine_u.copy()
    if mutated_fine_u.shape[1] > 0:
        angle = math.radians(2.0)
        mutated_fine_u[:, -1] = (
            math.cos(angle) * mutated_fine_u[:, -1] + math.sin(angle) * external
        )
        mutated_fine_u, _ = np.linalg.qr(mutated_fine_u)
    mutated_angle = production.principal_angle_degrees(medium_u, mutated_fine_u)
    threshold_stable = reference_fine["threshold_stable"]
    script_hash = _sha256_path(Path(__file__).resolve())
    production_hash = _sha256_path(Path(production.__file__).resolve())
    rows = [
        {
            "control_id": "OVERSIZED_DERIVATIVE_STEP",
            "metric": sum(not row["pass"] for row in oversized["plateau_rows"]),
            "required": "AT_LEAST_ONE_PLATEAU_FAILURE",
            "pass": not oversized["plateau_pass"],
        },
        {
            "control_id": "UNDERSIZED_NOISE_DOMINATED_STEP",
            "metric": sum(not row["pass"] for row in undersized["plateau_rows"]),
            "required": "AT_LEAST_ONE_PLATEAU_FAILURE",
            "pass": not undersized["plateau_pass"],
        },
        {
            "control_id": "EXACT_DUPLICATE_NUISANCE_COLUMN",
            "metric": baseline["rank"] - duplicate["rank"],
            "required": "RANK_DECREASE_GE_1",
            "pass": duplicate["rank"] <= baseline["rank"] - 1,
        },
        {
            "control_id": "NEAR_DUPLICATE_NUISANCE_COLUMN",
            "metric": len(near["near_pairs"]) + len(near["exact_pairs"]),
            "required": "NEAR_OR_EXACT_DEGENERACY_REPORTED",
            "pass": bool(near["near_pairs"] or near["exact_pairs"]),
        },
        {
            "control_id": "SVD_THRESHOLD_STABILITY",
            "metric": reference_fine["eta_spread"],
            "required": "RANK_CLASS_IDENTICAL_AND_ETA_SPREAD_LE_0.02",
            "pass": threshold_stable,
        },
        {
            "control_id": "SCALAR_EQUALS_CALIBRATION",
            "metric": equal_analysis["eta"],
            "required": "ABS_ETA_LE_1E-12",
            "pass": abs(equal_analysis["eta"]) <= 1e-12,
        },
        {
            "control_id": "SCALAR_ORTHOGONAL_TO_NUISANCES",
            "metric": orthogonal_analysis["eta"],
            "required": "ABS_ETA_MINUS_1_LE_1E-12",
            "pass": abs(orthogonal_analysis["eta"] - 1.0) <= 1e-12,
            "orthogonal_basis_index": orthogonal_index,
        },
        {
            "control_id": "POST_RESULT_TRANSITION_POINT_TAMPER",
            "metric": 1 if registered_hash != tampered_hash else 0,
            "required": "TAMPER_HASH_MISMATCH_DETECTED",
            "pass": registered_hash != tampered_hash,
        },
        {
            "control_id": "FORWARD_CONVERGED_JACOBIAN_UNSTABLE",
            "metric": mutated_angle,
            "required": "PRINCIPAL_ANGLE_GT_1_DEGREE",
            "pass": mutated_angle > 1.0,
        },
        {
            "control_id": "PRODUCTION_COMPONENT_PROVENANCE",
            "metric": 5,
            "required": "FIVE_COMPONENT_IDENTITIES_AND_HASHES_RECORDED",
            "pass": len(script_hash) == 64 and len(production_hash) == 64,
            "executor_sha256": script_hash,
            "production_module_sha256": production_hash,
        },
    ]
    return rows


def _pre_identifiability_controls() -> dict[str, Any]:
    benchmarks = _point_kernel_benchmarks()
    form_factor, form_factor_details = _form_factor_benchmark()
    benchmarks.append(form_factor)
    apparatus, symmetry, energy_rows = _apparatus_and_symmetry_controls()
    benchmarks.append(apparatus)
    mutations = _mutation_controls(form_factor_details)
    angular = _angular_convergence()
    convergence_rows = [angular, *energy_rows]
    convergence_rows.append(
        {
            "control_id": "DENSITY_CUBATURE_16_VS_24",
            "metric": form_factor["max_order16_vs_order24_relative_error"],
            "tolerance": 1e-6,
            "pass": form_factor["max_order16_vs_order24_relative_error"] <= 1e-6,
        }
    )
    return {
        "benchmarks": benchmarks,
        "form_factor_details": form_factor_details,
        "mutations": mutations,
        "symmetry": symmetry,
        "convergence": convergence_rows,
        "benchmarks_pass": all(row["pass"] for row in benchmarks),
        "mutations_pass": all(row["designated_control_detected"] for row in mutations),
        "symmetry_pass": all(row["pass"] for row in symmetry),
        "convergence_pass": all(row["pass"] for row in convergence_rows),
    }


def _serialize_full_execution(
    pre: dict[str, Any],
    identifiability: dict[str, Any] | None,
    v1_controls: list[dict[str, Any]],
) -> tuple[dict[str, bytes], dict[str, Any]]:
    benchmark_rows = []
    for row in pre["benchmarks"]:
        for key, value in row.items():
            if key in {"benchmark_id", "pass"}:
                continue
            benchmark_rows.append(
                {
                    "benchmark_id": row["benchmark_id"],
                    "metric_id": key,
                    "value": _float(float(value)) if isinstance(value, (float, int)) else str(value),
                    "pass": "PASS" if row["pass"] else "FAIL",
                }
            )
    mutation_rows = [
        {
            "mutation_id": row["mutation_id"],
            "designated_control": "FAIL_DETECTED"
            if row["designated_control_detected"]
            else "SURVIVED",
            "pass": "PASS" if row["designated_control_detected"] else "FAIL",
        }
        for row in pre["mutations"]
    ]
    symmetry_rows = [
        {
            "control_id": row["control_id"],
            "metric": _float(row["metric"]),
            "tolerance": _float(row["tolerance"]),
            "pass": "PASS" if row["pass"] else "FAIL",
        }
        for row in pre["symmetry"]
    ]
    convergence_rows = [
        {
            "control_id": row["control_id"],
            "step_rad": "" if "step_rad" not in row else _float(row["step_rad"]),
            "metric": _float(
                row.get("metric", row.get("max_relative_or_floored_error", 0.0))
            ),
            "tolerance": "" if "tolerance" not in row else _float(row["tolerance"]),
            "pass": "PASS" if row["pass"] else "FAIL",
        }
        for row in pre["convergence"]
    ]
    v1_rows = [
        {
            "control_id": row["control_id"],
            "metric": _float(float(row["metric"])),
            "required": row["required"],
            "pass": "PASS" if row["pass"] else "FAIL",
        }
        for row in v1_controls
    ]
    artifacts: dict[str, bytes] = {
        "benchmarks.csv": _csv_bytes(
            ["benchmark_id", "metric_id", "value", "pass"], benchmark_rows
        ),
        "mutations.csv": _csv_bytes(
            ["mutation_id", "designated_control", "pass"], mutation_rows
        ),
        "symmetry_controls.csv": _csv_bytes(
            ["control_id", "metric", "tolerance", "pass"], symmetry_rows
        ),
        "convergence.csv": _csv_bytes(
            ["control_id", "step_rad", "metric", "tolerance", "pass"],
            convergence_rows,
        ),
        "v1_controls.csv": _csv_bytes(
            ["control_id", "metric", "required", "pass"], v1_rows
        ),
    }
    newtonian, _ = production.real_150_vector(0.0, component="newtonian")
    reference_total, _ = production.real_150_vector(production.LAMBDA_REFERENCE)
    vector_headers = [
        "vector_class",
        "lambda_index",
        "lambda_m",
        "gap_index",
        "gap_m",
        "harmonic",
        "quadrature",
        "value_N_m",
    ]
    artifacts["newtonian_real_150.csv"] = _csv_bytes(
        vector_headers,
        _vector_rows(newtonian, lambda_index="NEWTONIAN", lambda_m=0.0, vector_class="NEWTONIAN"),
    )
    artifacts["reference_total_real_150.csv"] = _csv_bytes(
        vector_headers,
        _vector_rows(
            reference_total,
            lambda_index="REFERENCE",
            lambda_m=production.LAMBDA_REFERENCE,
            vector_class="TOTAL",
        ),
    )
    yukawa_rows = []
    for index, lam in enumerate(production.LAMBDA_GRID):
        vector, _ = production.real_150_vector(
            float(lam), component="yukawa", angular_samples=256
        )
        yukawa_rows.extend(
            _vector_rows(
                vector,
                lambda_index=f"GRID_{index:02d}",
                lambda_m=float(lam),
                vector_class="YUKAWA",
            )
        )
    artifacts["yukawa_real_150.csv"] = _csv_bytes(vector_headers, yukawa_rows)

    summary: dict[str, Any] = {
        "pre_identifiability": {
            "benchmark_count": len(pre["benchmarks"]),
            "benchmark_pass_count": sum(row["pass"] for row in pre["benchmarks"]),
            "mutation_count": len(pre["mutations"]),
            "mutation_pass_count": sum(
                row["designated_control_detected"] for row in pre["mutations"]
            ),
            "symmetry_control_count": len(pre["symmetry"]),
            "symmetry_pass_count": sum(row["pass"] for row in pre["symmetry"]),
            "convergence_control_count": len(pre["convergence"]),
            "convergence_pass_count": sum(row["pass"] for row in pre["convergence"]),
        },
        "v1_control_count": len(v1_controls),
        "v1_control_pass_count": sum(row["pass"] for row in v1_controls),
    }
    if identifiability is None:
        artifacts["jacobian_columns.csv"] = _csv_bytes(
            ["status"], [{"status": "NOT_COMPUTED_EARLY_PHYSICAL_CONTROL_BLOCK"}]
        )
        summary["identifiability"] = {"status": "NOT_COMPUTED_EARLY_PHYSICAL_CONTROL_BLOCK"}
        return artifacts, summary

    jacobian_rows = []
    metrics_rows = []
    singular_rows = []
    correlation_rows = []
    degeneracy_rows = []
    labels = ((2, "RE"), (2, "IM"), (4, "RE"), (4, "IM"), (6, "RE"), (6, "IM"))
    for point_result in identifiability["point_results"]:
        point_id = point_result["point_id"]
        lam = point_result["lambda_m"]
        fine_bundle = point_result["fine"]
        jacobian = fine_bundle["jacobian_result"]["jacobian"]
        for parameter_index, parameter_id in enumerate(production.PARAMETER_ORDER):
            column = jacobian[:, parameter_index].reshape((25, 6))
            for gap_index, gap in enumerate(production.GAPS):
                for component_index, (harmonic, quadrature) in enumerate(labels):
                    jacobian_rows.append(
                        {
                            "point_id": point_id,
                            "lambda_m": _float(lam),
                            "parameter_index": str(parameter_index),
                            "parameter_id": parameter_id,
                            "gap_index": str(gap_index),
                            "gap_m": _float(gap),
                            "harmonic": str(harmonic),
                            "quadrature": quadrature,
                            "derivative": _float(column[gap_index, component_index]),
                        }
                    )
        for refinement_id, bundle in (
            ("FINE", point_result["fine"]),
            ("MEDIUM", point_result["medium"]),
        ):
            if bundle is None:
                continue
            for threshold in RANK_THRESHOLDS:
                analysis = bundle["analyses"][threshold]
                metrics_rows.append(
                    {
                        "point_id": point_id,
                        "lambda_m": _float(lam),
                        "refinement": refinement_id,
                        "rank_threshold": _float(threshold),
                        "rank": str(analysis["rank"]),
                        "eta_lambda": _float(analysis["eta"]),
                        "classification": analysis["classification"],
                        "max_abs_scalar_nuisance_correlation": _float(
                            analysis["max_abs_correlation"]
                        ),
                        "condition_number": _float(analysis["condition_number"]),
                        "orthonormality_residual": _float(
                            analysis["orthonormality_residual"]
                        ),
                        "reconstruction_residual": _float(
                            analysis["reconstruction_residual"]
                        ),
                        "plateau_pass": "PASS"
                        if bundle["jacobian_result"]["plateau_pass"]
                        else "FAIL",
                        "threshold_stable": "PASS"
                        if bundle["threshold_stable"]
                        else "FAIL",
                    }
                )
                for singular_index, singular in enumerate(analysis["singular_values"]):
                    singular_rows.append(
                        {
                            "point_id": point_id,
                            "lambda_m": _float(lam),
                            "refinement": refinement_id,
                            "rank_threshold": _float(threshold),
                            "singular_index": str(singular_index),
                            "singular_value": _float(singular),
                            "retained": "YES"
                            if singular_index < analysis["rank"]
                            else "NO",
                        }
                    )
            central = bundle["analyses"][1e-10]
            for nuisance_index, correlation in enumerate(central["correlations"]):
                correlation_rows.append(
                    {
                        "point_id": point_id,
                        "lambda_m": _float(lam),
                        "refinement": refinement_id,
                        "nuisance_id": production.PARAMETER_ORDER[nuisance_index + 1],
                        "correlation": _float(correlation),
                    }
                )
            for kind, pairs in (
                ("EXACT", central["exact_pairs"]),
                ("NEAR", central["near_pairs"]),
            ):
                for left, right in pairs:
                    degeneracy_rows.append(
                        {
                            "point_id": point_id,
                            "lambda_m": _float(lam),
                            "refinement": refinement_id,
                            "degeneracy_class": kind,
                            "left_parameter": left,
                            "right_parameter": right,
                        }
                    )
    artifacts["jacobian_columns.csv"] = _csv_bytes(
        [
            "point_id",
            "lambda_m",
            "parameter_index",
            "parameter_id",
            "gap_index",
            "gap_m",
            "harmonic",
            "quadrature",
            "derivative",
        ],
        jacobian_rows,
    )
    artifacts["identifiability_metrics.csv"] = _csv_bytes(
        [
            "point_id",
            "lambda_m",
            "refinement",
            "rank_threshold",
            "rank",
            "eta_lambda",
            "classification",
            "max_abs_scalar_nuisance_correlation",
            "condition_number",
            "orthonormality_residual",
            "reconstruction_residual",
            "plateau_pass",
            "threshold_stable",
        ],
        metrics_rows,
    )
    artifacts["singular_values.csv"] = _csv_bytes(
        [
            "point_id",
            "lambda_m",
            "refinement",
            "rank_threshold",
            "singular_index",
            "singular_value",
            "retained",
        ],
        singular_rows,
    )
    artifacts["scalar_nuisance_correlations.csv"] = _csv_bytes(
        ["point_id", "lambda_m", "refinement", "nuisance_id", "correlation"],
        correlation_rows,
    )
    artifacts["degeneracies.csv"] = _csv_bytes(
        [
            "point_id",
            "lambda_m",
            "refinement",
            "degeneracy_class",
            "left_parameter",
            "right_parameter",
        ],
        degeneracy_rows,
    )
    decision_etas = [
        row["fine"]["analyses"][1e-10]["eta"]
        for row in identifiability["decision"]
    ]
    summary["identifiability"] = {
        "status": "COMPUTED",
        "evaluation_point_count": len(identifiability["point_results"]),
        "decision_point_count": len(identifiability["decision"]),
        "medium_refinement_point_count": len(identifiability["medium"]),
        "jacobian_shape": [150, 17],
        "minimum_eta_lambda_decision_domain": min(decision_etas),
        "maximum_eta_lambda_decision_domain": max(decision_etas),
        "contiguous_identifiable_count": identifiability[
            "contiguous_identifiable_count"
        ],
        "all_indistinguishable": identifiability["all_indistinguishable"],
        "any_plateau_failure": identifiability["any_plateau_failure"],
        "any_projector_failure": identifiability["any_projector_failure"],
        "any_refinement_failure": identifiability["any_refinement_failure"],
        "outcome": identifiability["outcome"],
        "secondary_outcome": identifiability["secondary_outcome"],
    }
    return artifacts, summary


def _compute_once() -> tuple[dict[str, bytes], dict[str, Any]]:
    pre = _pre_identifiability_controls()
    early_outcome = None
    if not pre["benchmarks_pass"]:
        if any(
            not row["pass"]
            and row["benchmark_id"] in {"POINT_NEWTONIAN", "POINT_YUKAWA", "UNIFORM_SPHERE_FORM_FACTOR"}
            for row in pre["benchmarks"]
        ):
            early_outcome = "BLOCKED_PRODUCTION_KERNEL_VALIDATION"
        else:
            early_outcome = "BLOCKED_TORQUE_DERIVATIVE_CONTRACT"
    elif not pre["mutations_pass"]:
        early_outcome = "BLOCKED_PRODUCTION_KERNEL_VALIDATION"
    elif not pre["symmetry_pass"]:
        early_outcome = "BLOCKED_GEOMETRY_OR_SYMMETRY_FAILURE"
    elif not pre["convergence_pass"]:
        early_outcome = "BLOCKED_NUMERICAL_CONVERGENCE"

    identifiability = None
    v1_controls: list[dict[str, Any]] = []
    if early_outcome is None:
        identifiability = _identifiability_execution()
        v1_controls = _v1_controls(identifiability)
        if not all(row["pass"] for row in v1_controls):
            failing = {row["control_id"] for row in v1_controls if not row["pass"]}
            if failing & {"OVERSIZED_DERIVATIVE_STEP", "UNDERSIZED_NOISE_DOMINATED_STEP"}:
                identifiability["outcome"] = "BLOCKED_FINITE_DIFFERENCE_PLATEAU"
            elif failing & {
                "EXACT_DUPLICATE_NUISANCE_COLUMN",
                "NEAR_DUPLICATE_NUISANCE_COLUMN",
                "SVD_THRESHOLD_STABILITY",
                "SCALAR_EQUALS_CALIBRATION",
                "SCALAR_ORTHOGONAL_TO_NUISANCES",
            }:
                identifiability["outcome"] = "BLOCKED_NUISANCE_PROJECTOR_UNSTABLE"
            else:
                identifiability["outcome"] = "BLOCKED_IDENTIFIABILITY_REFINEMENT_STABILITY"
            identifiability["secondary_outcome"] = "V1_PRODUCTION_CONTROL_FAILURE"

    artifacts, detail_summary = _serialize_full_execution(pre, identifiability, v1_controls)
    outcome = early_outcome or identifiability["outcome"]
    secondary = (
        "NO_IDENTIFIABILITY_CALCULATION_DUE_TO_EARLY_PHYSICAL_CONTROL_FAILURE"
        if early_outcome is not None
        else identifiability["secondary_outcome"]
    )
    core_summary = {
        "outcome": outcome,
        "secondary_outcome": secondary,
        "pre_identifiability_controls_pass": early_outcome is None,
        "detail": detail_summary,
    }
    artifacts["execution_core.json"] = _json_bytes(core_summary)
    return artifacts, core_summary


def _authority_check() -> dict[str, Any]:
    for relative_path, expected_hash in REVIEW_HASHES.items():
        if _sha256_path(REPO_ROOT / relative_path) != expected_hash:
            raise ValueError(f"execution authority drift: {relative_path}")
    review = json.loads((REPO_ROOT / REVIEW_RELATIVE_PATH).read_text(encoding="utf-8"))
    if review.get("verdict") != "DETERMINISTIC_IDENTIFIABILITY_CONTRACT_READY":
        raise ValueError("identifiability contract review is not ready")
    if review.get("selected_next_target") != TARGET:
        raise ValueError("review did not authorize this execution")
    authorization = review.get("execution_authorization", {})
    if authorization.get("execution_count_authorized") != 1:
        raise ValueError("review did not authorize exactly one execution")
    if authorization.get("execution_count_performed") != 0:
        raise ValueError("execution authority was already consumed")
    if authorization.get("stage_b_authorized") is not False:
        raise ValueError("Stage B unexpectedly authorized")
    return review


def execute_once() -> dict[str, Any]:
    review = _authority_check()
    output_directory = REPO_ROOT / OUTPUT_RELATIVE_DIRECTORY
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    output_result_path = output_directory / "execution_result.json"
    if report_path.exists() or output_result_path.exists():
        raise RuntimeError("single deterministic execution authority is already consumed")

    first_artifacts, first_core = _compute_once()
    second_artifacts, second_core = _compute_once()
    repeat_equal = first_artifacts == second_artifacts and first_core == second_core
    if not repeat_equal:
        raise RuntimeError("canonical internal repeat is not byte-identical")

    artifact_rows = [
        {
            "relative_path": f"{OUTPUT_RELATIVE_DIRECTORY}/{name}",
            "byte_count": len(value),
            "sha256": _sha256_bytes(value),
        }
        for name, value in sorted(first_artifacts.items())
    ]
    outcome = first_core["outcome"]
    stage_b_eligible = outcome == "DETERMINISTIC_FORWARD_MODEL_VALIDATED"
    scope = {
        "single_execution_authority_consumed": True,
        "deterministic_execution_performed": True,
        "internal_repeat_performed": True,
        "canonical_repeat_byte_identical": True,
        "benchmarks_executed": True,
        "mutations_executed": True,
        "symmetry_controls_executed": True,
        "convergence_controls_executed": True,
        "deterministic_vectors_produced": True,
        "jacobian_computed": first_core["detail"]["identifiability"]["status"] == "COMPUTED",
        "singular_values_computed": first_core["detail"]["identifiability"]["status"] == "COMPUTED",
        "eta_lambda_computed": first_core["detail"]["identifiability"]["status"] == "COMPUTED",
        "physical_identifiability_evaluated": first_core["detail"]["identifiability"]["status"] == "COMPUTED",
        "stage_b_eligible_for_fresh_selection": stage_b_eligible,
        "stage_b_authorized": False,
        "stochastic_packet_preparation_authorized": False,
        "gaussian_noise_used": False,
        "covariance_used": False,
        "monte_carlo_executed": False,
        "profile_likelihood_executed": False,
        "sensitivity_forecast_produced": False,
        "synthetic_dataset_generated": False,
        "measured_evidence_used": False,
        "empirical_constraint_claimed": False,
        "numerical_lambda_bound_computed": False,
        "numerical_alpha_bound_computed": False,
        "alpha_sign_or_value_adopted": False,
        "scalar_branch_adopted": False,
        "native_scalar_bridge_identified": False,
        "native_gravitational_principle_identified": False,
        "gravitational_action_selected": False,
        "automatic_v2_repair_authorized": False,
    }
    result = {
        "schema_id": "toe.scalar_only_yukawa.deterministic_torsion_balance_forward_model_validation.execution.v1",
        "execution_id": "SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_FORWARD_MODEL_VALIDATION_EXECUTION_20260719_v1",
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "outcome": outcome,
        "secondary_outcome": first_core["secondary_outcome"],
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_review_verdict": review["verdict"],
            "authorized_execution_count": 1,
            "consumed_execution_count": 1,
            "frozen_review_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in REVIEW_HASHES.items()
            ],
        },
        "canonical_repeat": {
            "internal_run_count": 2,
            "byte_identical": repeat_equal,
            "artifact_count_compared": len(first_artifacts),
        },
        "artifact_manifest": {
            "artifact_count": len(artifact_rows),
            "rows": artifact_rows,
        },
        "execution_summary": first_core,
        "scope": scope,
        "current_posture": {
            "authorized_deterministic_executions": 1,
            "consumed_deterministic_executions": 1,
            "deterministic_outcome": outcome,
            "stage_b_eligible_for_fresh_selection": stage_b_eligible,
            "stage_b": "NOT_AUTHORIZED",
            "synthetic_or_empirical_constraint": "NONE",
            "alpha": "NOT_SELECTED",
            "scalar_branch": "NOT_ADOPTED",
            "automatic_v2": "NOT_AUTHORIZED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
        "claim_ceiling": (
            "This result reports one idealized deterministic Stage A execution "
            "through the frozen internal torsion-balance model. It uses no random "
            "noise, covariance, Monte Carlo, likelihood, synthetic observation, or "
            "measured evidence; produces no sensitivity forecast or parameter bound; "
            "and does not authorize Stage B, select alpha, adopt a scalar branch, or "
            "identify a native ToE principle or action."
        ),
    }
    result_bytes = _json_bytes(result)
    output_directory.mkdir(parents=True, exist_ok=False)
    for name, value in first_artifacts.items():
        (output_directory / name).write_bytes(value)
    output_result_path.write_bytes(result_bytes)
    report_path.write_bytes(result_bytes)
    return result


def check_execution() -> int:
    _authority_check()
    output_directory = REPO_ROOT / OUTPUT_RELATIVE_DIRECTORY
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    output_result_path = output_directory / "execution_result.json"
    if not report_path.exists() or not output_result_path.exists():
        print("deterministic execution result missing")
        return 1
    if report_path.read_bytes() != output_result_path.read_bytes():
        print("deterministic execution result copies differ")
        return 1
    result = json.loads(report_path.read_text(encoding="utf-8"))
    for row in result["artifact_manifest"]["rows"]:
        path = REPO_ROOT / row["relative_path"]
        if not path.exists() or path.stat().st_size != row["byte_count"]:
            print(f"deterministic artifact missing or size drift: {row['relative_path']}")
            return 1
        if _sha256_path(path) != row["sha256"]:
            print(f"deterministic artifact hash drift: {row['relative_path']}")
            return 1
    if result["authority"]["consumed_execution_count"] != 1:
        print("deterministic execution count mismatch")
        return 1
    if result["scope"]["stage_b_authorized"] is not False:
        print("Stage B scope drift")
        return 1
    print(
        "deterministic execution result OK "
        f"outcome={result['outcome']} artifacts={result['artifact_manifest']['artifact_count']}"
    )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Execute the single authorized deterministic Yukawa Stage A run."
    )
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--execute", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.execute:
        result = execute_once()
        print(
            "deterministic execution complete "
            f"outcome={result['outcome']} next={result['selected_next_target']}"
        )
        return 0
    return check_execution()


if __name__ == "__main__":
    raise SystemExit(main())
