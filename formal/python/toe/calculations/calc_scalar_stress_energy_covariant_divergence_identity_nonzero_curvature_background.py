from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
from pathlib import Path
from typing import Any

import numpy as np

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
CALCULATION_ID = (
    "CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-IDENTITY-NONZERO-"
    "CURVATURE-BACKGROUND-v0"
)
CAPTURED_AT_UTC = "2026-07-09T00:00:00Z"
GUARDRAIL_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_"
    "NONZERO_CURVATURE_BACKGROUND_GUARDRAIL_PACKET_20260709_v0.json"
)
SCRIPT_RELATIVE_PATH = (
    "formal/python/toe/calculations/"
    "calc_scalar_stress_energy_covariant_divergence_identity_"
    "nonzero_curvature_background.py"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/calculations/"
    "test_calc_scalar_stress_energy_covariant_divergence_identity_"
    "nonzero_curvature_background.py"
)
OUTPUT_RELATIVE_PATH = (
    "formal/output/CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-IDENTITY-"
    "NONZERO-CURVATURE-BACKGROUND-v0.json"
)
MANIFEST_RELATIVE_PATH = (
    "formal/output/CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-IDENTITY-"
    "NONZERO-CURVATURE-BACKGROUND-MANIFEST-v0.json"
)
RESULT_REVIEW_TARGET = (
    "review_calc_scalar_stress_energy_covariant_divergence_identity_"
    "nonzero_curvature_background_v0_result"
)
THRESHOLD_REPAIR_TARGET = (
    "repair_calc_scalar_stress_energy_covariant_divergence_identity_nonzero_"
    "curvature_background_v0_threshold_failure"
)
EXECUTION_COMMAND = (
    "python -m formal.python.toe.calculations."
    "calc_scalar_stress_energy_covariant_divergence_identity_"
    "nonzero_curvature_background"
)

BACKGROUND_GEOMETRY_CLASSIFICATION = (
    "fixed_nonzero_curvature_1plus1_de_sitter_patch"
)
GUARDRAIL_GEOMETRY_CLASSIFICATION = (
    "fixed_1_plus_1_de_sitter_conformal_patch"
)
AMPLITUDE = 0.2
WAVE_NUMBER = 2.0
MASS = 0.0
HUBBLE_PARAMETER = 0.2
ETA_DOMAIN = (0.0, 1.0)
TIME_SLICES = (0.0, 0.37, 0.91)
RESOLUTIONS = (64, 128, 256, 512)
OMEGA_ON = 2.0
OMEGA_OFF = 2.2
EXACT_OFF_SHELL_COEFFICIENT = 0.84
EXPECTED_SCALAR_CURVATURE = 0.08
RELATIVE_ERROR_FLOOR = 1e-14

MINIMUM_CONVERGENCE_ORDER = 1.8
MAXIMUM_FINEST_OFF_SHELL_RELATIVE_ERROR = 0.02
MAXIMUM_COEFFICIENT_ERROR = 1e-12
MINIMUM_OFF_TO_ON_DIVERGENCE_RATIO = 100.0
MAXIMUM_METRIC_COMPATIBILITY_ERROR = 1e-12
MAXIMUM_FLAT_LIMIT_DISCREPANCY = 1e-12
MAXIMUM_CURVATURE_ROUTE_DISCREPANCY = 1e-12
MINIMUM_ABSOLUTE_SCALAR_CURVATURE = 0.05
MINIMUM_NAIVE_PARTIAL_ERROR_RATIO = 100.0
MINIMUM_CURVATURE_OMISSION_DISCREPANCY = 0.04
MINIMUM_FROZEN_CONNECTION_ERROR_RATIO = 50.0

EQUATION_ID = "EQ-QFT-SCALAR-COVARIANT-STRESS-DIVERGENCE-IDENTITY-v0"


def canonical_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(
            payload,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
            allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def centered_periodic_difference(values: np.ndarray, dx: float) -> np.ndarray:
    return (np.roll(values, -1) - np.roll(values, 1)) / (2.0 * dx)


def rms(values: np.ndarray) -> float:
    return float(np.sqrt(np.mean(np.square(values))))


def combined_rms(component_eta: np.ndarray, component_x: np.ndarray) -> float:
    return float(
        np.sqrt(np.mean(np.square(component_eta) + np.square(component_x)))
    )


def scale_factor(time: float, hubble_parameter: float = HUBBLE_PARAMETER) -> float:
    denominator = 1.0 - hubble_parameter * time
    if denominator <= 0.0:
        raise ValueError("time lies outside the frozen conformal coordinate patch")
    return 1.0 / denominator


def logarithmic_scale_derivative(
    time: float,
    hubble_parameter: float = HUBBLE_PARAMETER,
) -> float:
    return hubble_parameter * scale_factor(time, hubble_parameter)


def _metric_derivative_data(
    *,
    time: float,
    hubble_parameter: float,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    """Return g, g^-1, partial g, and partial-partial g.

    The derivative arrays are coordinate-generic inputs to the independent
    tensor reconstruction.  They do not call the conformal curvature formula.
    """

    a = scale_factor(time, hubble_parameter)
    q = logarithmic_scale_derivative(time, hubble_parameter)
    q_prime = (hubble_parameter * a) ** 2
    metric = np.array([[-a**2, 0.0], [0.0, a**2]], dtype=np.float64)
    inverse_metric = np.array(
        [[-(a**-2), 0.0], [0.0, a**-2]], dtype=np.float64
    )
    metric_derivative = np.zeros((2, 2, 2), dtype=np.float64)
    metric_derivative[0] = 2.0 * q * metric
    metric_second_derivative = np.zeros((2, 2, 2, 2), dtype=np.float64)
    metric_second_derivative[0, 0] = (2.0 * q_prime + 4.0 * q**2) * metric
    return metric, inverse_metric, metric_derivative, metric_second_derivative


def _connection_and_derivative_from_metric(
    *,
    metric: np.ndarray,
    inverse_metric: np.ndarray,
    metric_derivative: np.ndarray,
    metric_second_derivative: np.ndarray,
) -> tuple[np.ndarray, np.ndarray]:
    gamma = np.zeros((2, 2, 2), dtype=np.float64)
    for rho in range(2):
        for mu in range(2):
            for nu in range(2):
                for sigma in range(2):
                    gamma[rho, mu, nu] += 0.5 * inverse_metric[rho, sigma] * (
                        metric_derivative[mu, sigma, nu]
                        + metric_derivative[nu, sigma, mu]
                        - metric_derivative[sigma, mu, nu]
                    )

    inverse_metric_derivative = np.zeros((2, 2, 2), dtype=np.float64)
    for kappa in range(2):
        for rho in range(2):
            for sigma in range(2):
                for alpha in range(2):
                    for beta in range(2):
                        inverse_metric_derivative[kappa, rho, sigma] -= (
                            inverse_metric[rho, alpha]
                            * metric_derivative[kappa, alpha, beta]
                            * inverse_metric[beta, sigma]
                        )

    gamma_derivative = np.zeros((2, 2, 2, 2), dtype=np.float64)
    for kappa in range(2):
        for rho in range(2):
            for mu in range(2):
                for nu in range(2):
                    for sigma in range(2):
                        first_derivative_bracket = (
                            metric_derivative[mu, sigma, nu]
                            + metric_derivative[nu, sigma, mu]
                            - metric_derivative[sigma, mu, nu]
                        )
                        second_derivative_bracket = (
                            metric_second_derivative[kappa, mu, sigma, nu]
                            + metric_second_derivative[kappa, nu, sigma, mu]
                            - metric_second_derivative[kappa, sigma, mu, nu]
                        )
                        gamma_derivative[kappa, rho, mu, nu] += 0.5 * (
                            inverse_metric_derivative[kappa, rho, sigma]
                            * first_derivative_bracket
                            + inverse_metric[rho, sigma]
                            * second_derivative_bracket
                        )
    return gamma, gamma_derivative


def reconstruct_curvature(
    *,
    time: float,
    hubble_parameter: float = HUBBLE_PARAMETER,
    omit_connection_derivatives: bool = False,
) -> dict[str, Any]:
    metric, inverse_metric, metric_derivative, metric_second_derivative = (
        _metric_derivative_data(
            time=time,
            hubble_parameter=hubble_parameter,
        )
    )
    gamma, gamma_derivative = _connection_and_derivative_from_metric(
        metric=metric,
        inverse_metric=inverse_metric,
        metric_derivative=metric_derivative,
        metric_second_derivative=metric_second_derivative,
    )
    if omit_connection_derivatives:
        gamma_derivative = np.zeros_like(gamma_derivative)

    riemann = np.zeros((2, 2, 2, 2), dtype=np.float64)
    for rho in range(2):
        for sigma in range(2):
            for mu in range(2):
                for nu in range(2):
                    value = (
                        gamma_derivative[mu, rho, nu, sigma]
                        - gamma_derivative[nu, rho, mu, sigma]
                    )
                    for lam in range(2):
                        value += gamma[rho, mu, lam] * gamma[lam, nu, sigma]
                        value -= gamma[rho, nu, lam] * gamma[lam, mu, sigma]
                    riemann[rho, sigma, mu, nu] = value

    ricci = np.zeros((2, 2), dtype=np.float64)
    for sigma in range(2):
        for nu in range(2):
            ricci[sigma, nu] = sum(
                riemann[rho, sigma, rho, nu] for rho in range(2)
            )
    scalar_curvature = float(np.sum(inverse_metric * ricci))
    ricci_reference = hubble_parameter**2 * metric
    return {
        "time_eta": time,
        "scalar_curvature": scalar_curvature,
        "ricci_tensor": ricci.tolist(),
        "ricci_relation_max_absolute_error": float(
            np.max(np.abs(ricci - ricci_reference))
        ),
        "riemann_tensor_max_absolute_component": float(
            np.max(np.abs(riemann))
        ),
        "nonzero_connection_component_count": int(
            np.count_nonzero(np.abs(gamma) > 0.0)
        ),
        "_gamma": gamma,
    }


def analytic_scalar_curvature(
    *,
    time: float,
    hubble_parameter: float = HUBBLE_PARAMETER,
) -> float:
    a = scale_factor(time, hubble_parameter)
    q_prime = (hubble_parameter * a) ** 2
    return 2.0 * a**-2 * q_prime


def metric_compatibility_max_error(
    *,
    time: float,
    hubble_parameter: float = HUBBLE_PARAMETER,
) -> float:
    metric, inverse_metric, metric_derivative, metric_second_derivative = (
        _metric_derivative_data(
            time=time,
            hubble_parameter=hubble_parameter,
        )
    )
    gamma = _connection_and_derivative_from_metric(
        metric=metric,
        inverse_metric=inverse_metric,
        metric_derivative=metric_derivative,
        metric_second_derivative=metric_second_derivative,
    )[0]
    covariant_derivative = np.zeros((2, 2, 2), dtype=np.float64)
    for derivative_index in range(2):
        for mu in range(2):
            for nu in range(2):
                value = metric_derivative[derivative_index, mu, nu]
                for rho in range(2):
                    value -= gamma[rho, derivative_index, mu] * metric[rho, nu]
                    value -= gamma[rho, derivative_index, nu] * metric[mu, rho]
                covariant_derivative[derivative_index, mu, nu] = value
    return float(np.max(np.abs(covariant_derivative)))


def _plane_wave_fields(
    x: np.ndarray,
    *,
    time: float,
    omega: float,
) -> dict[str, np.ndarray]:
    theta = WAVE_NUMBER * x - omega * time
    phi = AMPLITUDE * np.cos(theta)
    phi_eta = AMPLITUDE * omega * np.sin(theta)
    phi_x = -AMPLITUDE * WAVE_NUMBER * np.sin(theta)
    return {
        "phi": phi,
        "phi_eta": phi_eta,
        "phi_x": phi_x,
        "phi_eta_eta": -(omega**2) * phi,
        "phi_x_eta": AMPLITUDE * WAVE_NUMBER * omega * np.cos(theta),
    }


def _connection_terms(
    stress: np.ndarray,
    gamma: np.ndarray,
) -> np.ndarray:
    terms = np.zeros((2, stress.shape[-1]), dtype=np.float64)
    for nu in range(2):
        for mu in range(2):
            for lam in range(2):
                terms[nu] += gamma[mu, mu, lam] * stress[lam, nu]
                terms[nu] += gamma[nu, mu, lam] * stress[mu, lam]
    return terms


def evaluate_time_slice(
    *,
    resolution: int,
    time: float,
    omega: float,
    hubble_parameter: float = HUBBLE_PARAMETER,
) -> dict[str, Any]:
    dx = 2.0 * math.pi / resolution
    x = np.arange(resolution, dtype=np.float64) * dx
    fields = _plane_wave_fields(x, time=time, omega=omega)
    phi = fields["phi"]
    phi_eta = fields["phi_eta"]
    phi_x = fields["phi_x"]
    phi_eta_eta = fields["phi_eta_eta"]
    phi_x_eta = fields["phi_x_eta"]

    metric, inverse_metric, metric_derivative, metric_second_derivative = (
        _metric_derivative_data(
            time=time,
            hubble_parameter=hubble_parameter,
        )
    )
    gamma = _connection_and_derivative_from_metric(
        metric=metric,
        inverse_metric=inverse_metric,
        metric_derivative=metric_derivative,
        metric_second_derivative=metric_second_derivative,
    )[0]
    a = scale_factor(time, hubble_parameter)
    q = logarithmic_scale_derivative(time, hubble_parameter)
    inverse_scale_squared = a**-2
    inverse_scale_fourth = a**-4

    raised_eta = inverse_metric[0, 0] * phi_eta
    raised_x = inverse_metric[1, 1] * phi_x
    contraction = inverse_scale_squared * (-phi_eta**2 + phi_x**2)
    bracket = 0.5 * contraction
    stress = np.zeros((2, 2, resolution), dtype=np.float64)
    stress[0, 0] = raised_eta**2 - inverse_metric[0, 0] * bracket
    stress[0, 1] = raised_eta * raised_x
    stress[1, 0] = stress[0, 1]
    stress[1, 1] = raised_x**2 - inverse_metric[1, 1] * bracket

    sum_squares = phi_eta**2 + phi_x**2
    dt_t00 = 0.5 * inverse_scale_fourth * (
        -4.0 * q * sum_squares
        + 2.0 * phi_eta * phi_eta_eta
        + 2.0 * phi_x * phi_x_eta
    )
    dt_t01 = inverse_scale_fourth * (
        4.0 * q * phi_eta * phi_x
        - phi_eta_eta * phi_x
        - phi_eta * phi_x_eta
    )
    temporal_derivative = np.stack([dt_t00, dt_t01])
    spatial_derivative = np.stack(
        [
            centered_periodic_difference(stress[1, 0], dx),
            centered_periodic_difference(stress[1, 1], dx),
        ]
    )
    partial_divergence = temporal_derivative + spatial_derivative
    correct_connection_terms = _connection_terms(stress, gamma)
    covariant_divergence = partial_divergence + correct_connection_terms

    coefficient = omega**2 - WAVE_NUMBER**2
    e_phi = inverse_scale_squared * coefficient * phi
    rhs = np.stack([e_phi * raised_eta, e_phi * raised_x])
    covariant_error = covariant_divergence - rhs
    naive_error = partial_divergence - rhs

    # This deliberately inconsistent control changes only the connection used
    # in the divergence.  The true scale factor, stress, and analytic partial
    # derivative above retain q(eta), as frozen by the guardrail.
    frozen_gamma = np.zeros_like(gamma)
    frozen_gamma[0, 0, 0] = hubble_parameter
    frozen_gamma[0, 1, 1] = hubble_parameter
    frozen_gamma[1, 0, 1] = hubble_parameter
    frozen_gamma[1, 1, 0] = hubble_parameter
    frozen_connection_terms = _connection_terms(stress, frozen_gamma)
    frozen_connection_error = (
        partial_divergence + frozen_connection_terms - rhs
    )

    expected_coefficient = (
        0.0 if math.isclose(omega, OMEGA_ON) else EXACT_OFF_SHELL_COEFFICIENT
    )
    exact_reference = expected_coefficient * inverse_scale_squared * phi
    denominator = 1.0 - hubble_parameter * time
    patch_singularity = (
        math.inf if hubble_parameter == 0.0 else 1.0 / hubble_parameter
    )

    return {
        "resolution_N": resolution,
        "time_eta": time,
        "dx": dx,
        "conformal_denominator": denominator,
        "scale_factor": a,
        "logarithmic_scale_derivative_q": q,
        "coordinate_distance_to_patch_singularity": patch_singularity - time,
        "equation_residual_coefficient_before_a_inverse_squared": coefficient,
        "covariant_divergence_norms": {
            "nu_eta": rms(covariant_divergence[0]),
            "nu_x": rms(covariant_divergence[1]),
            "combined": combined_rms(
                covariant_divergence[0], covariant_divergence[1]
            ),
        },
        "rhs_norms": {
            "nu_eta": rms(rhs[0]),
            "nu_x": rms(rhs[1]),
            "combined": combined_rms(rhs[0], rhs[1]),
        },
        "covariant_identity_absolute_error_norms": {
            "nu_eta": rms(covariant_error[0]),
            "nu_x": rms(covariant_error[1]),
            "combined": combined_rms(covariant_error[0], covariant_error[1]),
        },
        "covariant_identity_relative_error_norms": {
            "nu_eta": rms(covariant_error[0])
            / max(rms(rhs[0]), RELATIVE_ERROR_FLOOR),
            "nu_x": rms(covariant_error[1])
            / max(rms(rhs[1]), RELATIVE_ERROR_FLOOR),
            "combined": combined_rms(covariant_error[0], covariant_error[1])
            / max(combined_rms(rhs[0], rhs[1]), RELATIVE_ERROR_FLOOR),
        },
        "negative_control_errors": {
            "naive_partial_divergence_combined": combined_rms(
                naive_error[0], naive_error[1]
            ),
            "inconsistent_frozen_connection_combined": combined_rms(
                frozen_connection_error[0], frozen_connection_error[1]
            ),
            "correct_covariant_combined": combined_rms(
                covariant_error[0], covariant_error[1]
            ),
        },
        "metric_compatibility_max_absolute_error": (
            metric_compatibility_max_error(
                time=time,
                hubble_parameter=hubble_parameter,
            )
        ),
        "exact_residual_reference": {
            "expected_coefficient_before_a_inverse_squared": expected_coefficient,
            "computed_coefficient_before_a_inverse_squared": coefficient,
            "coefficient_absolute_error": abs(coefficient - expected_coefficient),
            "field_residual_absolute_error_norm": rms(e_phi - exact_reference),
            "field_residual_relative_error_norm": rms(e_phi - exact_reference)
            / max(rms(exact_reference), RELATIVE_ERROR_FLOOR),
        },
        "_arrays": {
            "covariant_divergence": covariant_divergence,
            "rhs": rhs,
            "covariant_error": covariant_error,
            "naive_error": naive_error,
            "frozen_connection_error": frozen_connection_error,
            "e_phi": e_phi,
            "exact_reference": exact_reference,
        },
    }


def _evaluate_flat_reference(
    *,
    resolution: int,
    time: float,
    omega: float,
) -> dict[str, np.ndarray]:
    dx = 2.0 * math.pi / resolution
    x = np.arange(resolution, dtype=np.float64) * dx
    fields = _plane_wave_fields(x, time=time, omega=omega)
    phi = fields["phi"]
    phi_eta = fields["phi_eta"]
    phi_x = fields["phi_x"]
    phi_eta_eta = fields["phi_eta_eta"]
    phi_x_eta = fields["phi_x_eta"]
    stress_00 = 0.5 * (phi_eta**2 + phi_x**2)
    stress_01 = -phi_eta * phi_x
    stress_11 = stress_00
    divergence = np.stack(
        [
            phi_eta * phi_eta_eta
            + phi_x * phi_x_eta
            + centered_periodic_difference(stress_01, dx),
            -(phi_eta_eta * phi_x + phi_eta * phi_x_eta)
            + centered_periodic_difference(stress_11, dx),
        ]
    )
    coefficient = omega**2 - WAVE_NUMBER**2
    e_phi = coefficient * phi
    rhs = np.stack([-e_phi * phi_eta, e_phi * phi_x])
    return {"divergence": divergence, "rhs": rhs}


def flat_limit_max_discrepancy() -> float:
    discrepancies: list[float] = []
    for resolution in RESOLUTIONS:
        for time in TIME_SLICES:
            for omega in (OMEGA_ON, OMEGA_OFF):
                covariant = evaluate_time_slice(
                    resolution=resolution,
                    time=time,
                    omega=omega,
                    hubble_parameter=0.0,
                )["_arrays"]
                direct = _evaluate_flat_reference(
                    resolution=resolution,
                    time=time,
                    omega=omega,
                )
                discrepancies.append(
                    float(
                        np.max(
                            np.abs(
                                covariant["covariant_divergence"]
                                - direct["divergence"]
                            )
                        )
                    )
                )
                discrepancies.append(
                    float(np.max(np.abs(covariant["rhs"] - direct["rhs"])))
                )
    return max(discrepancies)


def _aggregate_resolution(
    *,
    resolution: int,
    omega: float,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    raw_rows = [
        evaluate_time_slice(
            resolution=resolution,
            time=time,
            omega=omega,
        )
        for time in TIME_SLICES
    ]
    public_rows = [
        {key: value for key, value in row.items() if key != "_arrays"}
        for row in raw_rows
    ]

    def concatenate(name: str, component: int | None = None) -> np.ndarray:
        values = [row["_arrays"][name] for row in raw_rows]
        if component is not None:
            values = [value[component] for value in values]
        return np.concatenate(values, axis=-1)

    divergence_eta = concatenate("covariant_divergence", 0)
    divergence_x = concatenate("covariant_divergence", 1)
    rhs_eta = concatenate("rhs", 0)
    rhs_x = concatenate("rhs", 1)
    error_eta = concatenate("covariant_error", 0)
    error_x = concatenate("covariant_error", 1)
    naive_eta = concatenate("naive_error", 0)
    naive_x = concatenate("naive_error", 1)
    frozen_eta = concatenate("frozen_connection_error", 0)
    frozen_x = concatenate("frozen_connection_error", 1)
    e_phi = concatenate("e_phi")
    exact_reference = concatenate("exact_reference")
    correct_error = combined_rms(error_eta, error_x)
    expected_coefficient = (
        0.0 if math.isclose(omega, OMEGA_ON) else EXACT_OFF_SHELL_COEFFICIENT
    )
    computed_coefficient = omega**2 - WAVE_NUMBER**2

    return {
        "resolution_N": resolution,
        "time_slice_count": len(TIME_SLICES),
        "covariant_divergence_norms": {
            "nu_eta": rms(divergence_eta),
            "nu_x": rms(divergence_x),
            "combined": combined_rms(divergence_eta, divergence_x),
        },
        "rhs_norms": {
            "nu_eta": rms(rhs_eta),
            "nu_x": rms(rhs_x),
            "combined": combined_rms(rhs_eta, rhs_x),
        },
        "covariant_identity_absolute_error_norms": {
            "nu_eta": rms(error_eta),
            "nu_x": rms(error_x),
            "combined": correct_error,
        },
        "covariant_identity_relative_error_norms": {
            "nu_eta": rms(error_eta) / max(rms(rhs_eta), RELATIVE_ERROR_FLOOR),
            "nu_x": rms(error_x) / max(rms(rhs_x), RELATIVE_ERROR_FLOOR),
            "combined": correct_error
            / max(combined_rms(rhs_eta, rhs_x), RELATIVE_ERROR_FLOOR),
        },
        "negative_control_errors": {
            "naive_partial_divergence_combined": combined_rms(
                naive_eta, naive_x
            ),
            "naive_to_correct_error_ratio": combined_rms(naive_eta, naive_x)
            / max(correct_error, RELATIVE_ERROR_FLOOR),
            "inconsistent_frozen_connection_combined": combined_rms(
                frozen_eta, frozen_x
            ),
            "inconsistent_frozen_connection_to_correct_error_ratio": (
                combined_rms(frozen_eta, frozen_x)
                / max(correct_error, RELATIVE_ERROR_FLOOR)
            ),
        },
        "exact_residual_reference": {
            "expected_coefficient_before_a_inverse_squared": expected_coefficient,
            "computed_coefficient_before_a_inverse_squared": computed_coefficient,
            "coefficient_absolute_error": abs(
                computed_coefficient - expected_coefficient
            ),
            "field_residual_absolute_error_norm": rms(e_phi - exact_reference),
            "field_residual_relative_error_norm": rms(e_phi - exact_reference)
            / max(rms(exact_reference), RELATIVE_ERROR_FLOOR),
        },
        "metric_compatibility_max_absolute_error": max(
            row["metric_compatibility_max_absolute_error"] for row in raw_rows
        ),
    }, public_rows


def _convergence_orders(values: list[float]) -> list[dict[str, float | int]]:
    return [
        {
            "coarse_N": RESOLUTIONS[index],
            "fine_N": RESOLUTIONS[index + 1],
            "order": math.log(values[index] / values[index + 1], 2.0),
        }
        for index in range(len(values) - 1)
    ]


def curvature_verification() -> dict[str, Any]:
    analytic_rows: list[dict[str, float]] = []
    component_rows: list[dict[str, Any]] = []
    omitted_rows: list[dict[str, float]] = []
    route_discrepancies: list[float] = []
    omission_discrepancies: list[float] = []
    ricci_errors: list[float] = []
    measured_values: list[float] = []
    for time in TIME_SLICES:
        analytic_value = analytic_scalar_curvature(time=time)
        component = reconstruct_curvature(time=time)
        omitted = reconstruct_curvature(
            time=time,
            omit_connection_derivatives=True,
        )
        measured = component["scalar_curvature"]
        analytic_rows.append(
            {"time_eta": time, "scalar_curvature": analytic_value}
        )
        component_rows.append(
            {key: value for key, value in component.items() if key != "_gamma"}
        )
        omitted_rows.append(
            {"time_eta": time, "bad_scalar_curvature": omitted["scalar_curvature"]}
        )
        route_discrepancies.append(abs(analytic_value - measured))
        omission_discrepancies.append(
            abs(measured - omitted["scalar_curvature"])
        )
        ricci_errors.append(component["ricci_relation_max_absolute_error"])
        measured_values.append(measured)
    return {
        "analytic_conformal_route": {
            "formula": "R = 2*a(eta)^(-2)*partial_eta q(eta) = 2*H^2",
            "rows": analytic_rows,
        },
        "independent_component_route": {
            "method": (
                "g,dg,ddg -> Gamma,dGamma -> Riemann -> Ricci -> scalar; "
                "analytic conformal scalar-curvature shortcut not used"
            ),
            "rows": component_rows,
        },
        "scalar_curvature_expected": EXPECTED_SCALAR_CURVATURE,
        "scalar_curvature_measured": float(np.mean(measured_values)),
        "maximum_route_agreement_absolute_error": max(route_discrepancies),
        "minimum_absolute_measured_scalar_curvature": min(
            abs(value) for value in measured_values
        ),
        "ricci_relation_max_absolute_error": max(ricci_errors),
        "curvature_derivative_omission_negative_control": {
            "operation": "omit all derivative-of-Gamma terms",
            "rows": omitted_rows,
            "minimum_absolute_discrepancy_from_correct_route": min(
                omission_discrepancies
            ),
            "failure_detected": (
                min(omission_discrepancies)
                >= MINIMUM_CURVATURE_OMISSION_DISCREPANCY
            ),
        },
    }


def patch_domain_safety() -> dict[str, Any]:
    eta_min, eta_max = ETA_DOMAIN
    singularity_eta = 1.0 / HUBBLE_PARAMETER
    domain_denominator_min = 1.0 - HUBBLE_PARAMETER * eta_max
    sampled_denominators = [
        1.0 - HUBBLE_PARAMETER * time for time in TIME_SLICES
    ]
    sampled_scale_factors = [scale_factor(time) for time in TIME_SLICES]
    sampled_distances = [singularity_eta - time for time in TIME_SLICES]
    return {
        "eta_domain": [eta_min, eta_max],
        "coordinate_patch_singularity_eta": singularity_eta,
        "minimum_one_minus_H_eta_over_domain": domain_denominator_min,
        "maximum_scale_factor_over_domain": 1.0 / domain_denominator_min,
        "minimum_coordinate_distance_to_patch_singularity_over_domain": (
            singularity_eta - eta_max
        ),
        "sampled_minimum_one_minus_H_eta": min(sampled_denominators),
        "sampled_maximum_scale_factor": max(sampled_scale_factors),
        "sampled_minimum_coordinate_distance_to_patch_singularity": min(
            sampled_distances
        ),
        "strictly_inside_coordinate_patch": domain_denominator_min > 0.0,
        "coordinate_patch_boundary_is_physical_curvature_singularity": False,
        "derived_invariant_not_additional_guardrail_threshold": True,
    }


def build_result(*, captured_at_utc: str = CAPTURED_AT_UTC) -> dict[str, Any]:
    on_aggregates: list[dict[str, Any]] = []
    on_rows: list[dict[str, Any]] = []
    off_aggregates: list[dict[str, Any]] = []
    off_rows: list[dict[str, Any]] = []
    for resolution in RESOLUTIONS:
        aggregate, rows = _aggregate_resolution(
            resolution=resolution,
            omega=OMEGA_ON,
        )
        on_aggregates.append(aggregate)
        on_rows.extend(rows)
        aggregate, rows = _aggregate_resolution(
            resolution=resolution,
            omega=OMEGA_OFF,
        )
        off_aggregates.append(aggregate)
        off_rows.extend(rows)

    on_errors = [
        row["covariant_divergence_norms"]["combined"] for row in on_aggregates
    ]
    off_errors = [
        row["covariant_identity_absolute_error_norms"]["combined"]
        for row in off_aggregates
    ]
    on_orders = _convergence_orders(on_errors)
    off_orders = _convergence_orders(off_errors)
    minimum_two_finest_order = min(
        row["order"] for row in [*on_orders[-2:], *off_orders[-2:]]
    )
    finest_on = on_aggregates[-1]
    finest_off = off_aggregates[-1]
    curvature = curvature_verification()
    patch_safety = patch_domain_safety()
    finest_off_relative_error = finest_off[
        "covariant_identity_relative_error_norms"
    ]["combined"]
    coefficient_error = finest_off["exact_residual_reference"][
        "coefficient_absolute_error"
    ]
    off_to_on_ratio = (
        finest_off["covariant_divergence_norms"]["combined"]
        / finest_on["covariant_divergence_norms"]["combined"]
    )
    metric_error = max(
        row["metric_compatibility_max_absolute_error"]
        for row in [*on_aggregates, *off_aggregates]
    )
    flat_discrepancy = flat_limit_max_discrepancy()
    naive_ratio = finest_on["negative_control_errors"][
        "naive_to_correct_error_ratio"
    ]
    frozen_ratios = [
        finest_on["negative_control_errors"][
            "inconsistent_frozen_connection_to_correct_error_ratio"
        ],
        finest_off["negative_control_errors"][
            "inconsistent_frozen_connection_to_correct_error_ratio"
        ],
    ]
    minimum_frozen_ratio = min(frozen_ratios)
    curvature_route_error = curvature[
        "maximum_route_agreement_absolute_error"
    ]
    minimum_curvature = curvature[
        "minimum_absolute_measured_scalar_curvature"
    ]
    curvature_omission_discrepancy = curvature[
        "curvature_derivative_omission_negative_control"
    ]["minimum_absolute_discrepancy_from_correct_route"]

    checks = {
        "two_finest_convergence_order_at_least_1_8": (
            minimum_two_finest_order >= MINIMUM_CONVERGENCE_ORDER
        ),
        "finest_combined_off_shell_relative_error_at_most_2_percent": (
            finest_off_relative_error <= MAXIMUM_FINEST_OFF_SHELL_RELATIVE_ERROR
        ),
        "exact_coefficient_error_at_most_1e_12": (
            coefficient_error <= MAXIMUM_COEFFICIENT_ERROR
        ),
        "finest_off_shell_divergence_over_100_times_on_shell": (
            off_to_on_ratio >= MINIMUM_OFF_TO_ON_DIVERGENCE_RATIO
        ),
        "metric_compatibility_error_at_most_1e_12": (
            metric_error <= MAXIMUM_METRIC_COMPATIBILITY_ERROR
        ),
        "flat_limit_discrepancy_at_most_1e_12": (
            flat_discrepancy <= MAXIMUM_FLAT_LIMIT_DISCREPANCY
        ),
        "curvature_route_discrepancy_at_most_1e_12": (
            curvature_route_error <= MAXIMUM_CURVATURE_ROUTE_DISCREPANCY
        ),
        "absolute_scalar_curvature_at_least_0_05": (
            minimum_curvature >= MINIMUM_ABSOLUTE_SCALAR_CURVATURE
        ),
        "naive_partial_divergence_error_ratio_at_least_100": (
            naive_ratio >= MINIMUM_NAIVE_PARTIAL_ERROR_RATIO
        ),
        "curvature_omission_discrepancy_at_least_0_04": (
            curvature_omission_discrepancy
            >= MINIMUM_CURVATURE_OMISSION_DISCREPANCY
        ),
        "inconsistent_frozen_connection_error_ratio_at_least_50": (
            minimum_frozen_ratio >= MINIMUM_FROZEN_CONNECTION_ERROR_RATIO
        ),
    }
    passed = all(checks.values())
    claim_label = "E-REPRO" if passed else "B-BLOCKED"
    next_target = RESULT_REVIEW_TARGET if passed else THRESHOLD_REPAIR_TARGET

    thresholds = {
        "minimum_convergence_order_two_finest_pairs": MINIMUM_CONVERGENCE_ORDER,
        "maximum_finest_combined_off_shell_relative_error": (
            MAXIMUM_FINEST_OFF_SHELL_RELATIVE_ERROR
        ),
        "maximum_exact_coefficient_absolute_error": MAXIMUM_COEFFICIENT_ERROR,
        "minimum_finest_off_to_on_divergence_norm_ratio": (
            MINIMUM_OFF_TO_ON_DIVERGENCE_RATIO
        ),
        "maximum_metric_compatibility_absolute_error": (
            MAXIMUM_METRIC_COMPATIBILITY_ERROR
        ),
        "maximum_flat_limit_absolute_discrepancy": (
            MAXIMUM_FLAT_LIMIT_DISCREPANCY
        ),
        "maximum_curvature_route_absolute_discrepancy": (
            MAXIMUM_CURVATURE_ROUTE_DISCREPANCY
        ),
        "minimum_absolute_scalar_curvature": MINIMUM_ABSOLUTE_SCALAR_CURVATURE,
        "minimum_naive_partial_divergence_identity_error_ratio": (
            MINIMUM_NAIVE_PARTIAL_ERROR_RATIO
        ),
        "minimum_curvature_omission_absolute_discrepancy": (
            MINIMUM_CURVATURE_OMISSION_DISCREPANCY
        ),
        "minimum_inconsistent_frozen_connection_identity_error_ratio": (
            MINIMUM_FROZEN_CONNECTION_ERROR_RATIO
        ),
        "all_thresholds_required": True,
    }
    threshold_evidence = {
        "minimum_observed_two_finest_convergence_order": minimum_two_finest_order,
        "finest_combined_off_shell_relative_error": finest_off_relative_error,
        "exact_coefficient_absolute_error": coefficient_error,
        "finest_off_to_on_divergence_norm_ratio": off_to_on_ratio,
        "metric_compatibility_max_absolute_error": metric_error,
        "flat_limit_max_absolute_discrepancy": flat_discrepancy,
        "curvature_route_max_absolute_discrepancy": curvature_route_error,
        "minimum_absolute_measured_scalar_curvature": minimum_curvature,
        "finest_on_shell_naive_to_correct_error_ratio": naive_ratio,
        "curvature_omission_minimum_absolute_discrepancy": (
            curvature_omission_discrepancy
        ),
        "finest_minimum_on_off_frozen_connection_to_correct_error_ratio": (
            minimum_frozen_ratio
        ),
    }

    return {
        "schema_id": f"{CALCULATION_ID}-RESULT",
        "calculation_id": CALCULATION_ID,
        "calculation_status": (
            "executed_pending_result_review" if passed else "executed_blocked"
        ),
        "captured_at_utc": captured_at_utc,
        "question": (
            "Numerically verify the scalar covariant stress-energy divergence "
            "identity on one fixed genuinely curved 1+1 de Sitter patch."
        ),
        "background_geometry_classification": BACKGROUND_GEOMETRY_CLASSIFICATION,
        "scalar_curvature_expected": EXPECTED_SCALAR_CURVATURE,
        "scalar_curvature_measured": curvature["scalar_curvature_measured"],
        "gravity_evolved": False,
        "einstein_tensor_source_tested": False,
        "two_dimensional_einstein_gravity_degenerate": True,
        "covariant_matter_identity_tested": True,
        "background_geometry": {
            "background_geometry_classification": (
                BACKGROUND_GEOMETRY_CLASSIFICATION
            ),
            "guardrail_geometry_classification": (
                GUARDRAIL_GEOMETRY_CLASSIFICATION
            ),
            "metric": "g_mu_nu = a(eta)^2 diag(-1,+1)",
            "scale_factor": "a(eta) = (1 - 0.2*eta)^(-1)",
            "metric_signature": "(-,+)",
            "scalar_curvature_expected": EXPECTED_SCALAR_CURVATURE,
            "scalar_curvature_measured": curvature[
                "scalar_curvature_measured"
            ],
            "genuinely_nonzero_curvature_test_executed": True,
            "curvature_test_claimed": True,
            "covariant_connection_test_claimed": True,
        },
        "curvature_verification": curvature,
        "patch_domain_safety": patch_safety,
        "interpretation": {
            "successful_result_establishes": (
                "the covariant scalar matter identity on one fixed genuinely "
                "curved 1+1 de Sitter background"
            ),
            "source_free_control_note": (
                "the exact plane wave uses the D=2 massless conformal equation "
                "structure and is not robustness evidence for massive, "
                "nonconformal, or higher-dimensional fields"
            ),
            "einstein_gravity_boundary": (
                "G_mu_nu is identically zero in two dimensions; this is not "
                "an ordinary Einstein-scalar source test"
            ),
        },
        "mathematical_convention": {
            "christoffel_definition": (
                "Gamma^rho_mu_nu = 1/2 g^rho_sigma "
                "(partial_mu g_sigma_nu + partial_nu g_sigma_mu - "
                "partial_sigma g_mu_nu)"
            ),
            "riemann_sign": (
                "R^rho_sigma_mu_nu = partial_mu Gamma^rho_nu_sigma - "
                "partial_nu Gamma^rho_mu_sigma + Gamma^rho_mu_lambda "
                "Gamma^lambda_nu_sigma - Gamma^rho_nu_lambda "
                "Gamma^lambda_mu_sigma"
            ),
            "ricci_contraction": "R_sigma_nu = R^rho_sigma_rho_nu",
            "stress_energy": (
                "T^{mu nu} = nabla^mu phi nabla^nu phi - g^{mu nu} "
                "[1/2 nabla_alpha phi nabla^alpha phi]"
            ),
            "field_residual": "E_phi = Box_g phi",
            "identity": "nabla_mu T^{mu nu} = E_phi nabla^nu phi",
        },
        "parameters": {
            "amplitude_A": AMPLITUDE,
            "wave_number_k": WAVE_NUMBER,
            "mass_m": MASS,
            "conformal_hubble_parameter_H": HUBBLE_PARAMETER,
            "eta_domain": list(ETA_DOMAIN),
            "spatial_domain": "[0,2*pi), periodic",
            "time_slices_eta": list(TIME_SLICES),
            "resolutions_N": list(RESOLUTIONS),
            "omega_on": OMEGA_ON,
            "omega_off": OMEGA_OFF,
            "exact_off_shell_coefficient_before_a_inverse_squared": (
                EXACT_OFF_SHELL_COEFFICIENT
            ),
        },
        "method": {
            "temporal_derivatives": "analytic",
            "metric_and_connection_derivatives": "analytic",
            "spatial_derivatives": (
                "second-order centered periodic finite differences"
            ),
            "component_norm": "RMS sqrt(mean(v_nu^2))",
            "combined_norm": "RMS sqrt(mean(v_eta^2 + v_x^2))",
            "space_time_combined_norm": (
                "RMS over all frozen time slices and periodic spatial points"
            ),
            "relative_error_floor": RELATIVE_ERROR_FLOOR,
        },
        "on_shell": {
            "control_role": "exact source-free covariant-conservation control",
            "forced_or_manufactured": False,
            "exact_residual": "E_phi = 0",
            "relative_error_against_zero_formed": False,
            "resolution_aggregates": on_aggregates,
            "time_slice_results": on_rows,
            "combined_absolute_divergence_convergence_orders": on_orders,
        },
        "off_shell": {
            "control_role": "deliberately off-shell unforced residual control",
            "forced_or_manufactured": False,
            "exact_reference": "E_phi = 0.84 * a(eta)^(-2) * phi",
            "resolution_aggregates": off_aggregates,
            "time_slice_results": off_rows,
            "combined_identity_error_convergence_orders": off_orders,
        },
        "negative_controls": {
            "naive_partial_divergence": {
                "description": "omit all connection terms from nabla_mu T^{mu nu}",
                "finest_on_shell_error_ratio": naive_ratio,
                "failure_detected": naive_ratio >= MINIMUM_NAIVE_PARTIAL_ERROR_RATIO,
            },
            "inconsistent_frozen_connection": {
                "description": (
                    "replace q(eta) by H only in the divergence connection "
                    "terms while retaining the true curved stress and partial "
                    "derivative"
                ),
                "eta_zero_slice_expected_to_match_correct_connection": True,
                "finest_on_shell_error_ratio": frozen_ratios[0],
                "finest_off_shell_error_ratio": frozen_ratios[1],
                "minimum_finest_on_off_error_ratio": minimum_frozen_ratio,
                "failure_detected": (
                    minimum_frozen_ratio >= MINIMUM_FROZEN_CONNECTION_ERROR_RATIO
                ),
            },
            "curvature_derivative_omission": curvature[
                "curvature_derivative_omission_negative_control"
            ],
        },
        "thresholds": thresholds,
        "threshold_evidence": threshold_evidence,
        "threshold_checks": checks,
        "frozen_threshold_count": len(checks),
        "all_thresholds_passed": passed,
        "claim": {
            "primary_label": claim_label,
            "claim_status": (
                "generated_pending_result_review"
                if passed
                else "blocked_threshold_failure"
            ),
            "claim_scope": (
                "scoped E-REPRO pending review for the scalar covariant "
                "stress-energy divergence identity on one fixed 1+1 de "
                "Sitter background"
            ),
            "claim_ceiling_level": 3,
            "next_work_status": next_target,
        },
        "existing_equation_id_reused": EQUATION_ID,
        "equation_compendium_edited": False,
        "boundary": {
            "calculation_executed": True,
            "gravity_evolved": False,
            "background_metric_evolved": False,
            "einstein_equation_solved": False,
            "einstein_tensor_source_tested": False,
            "two_dimensional_einstein_gravity_degenerate": True,
            "einstein_tensor_identically_zero_in_two_dimensions": True,
            "ordinary_einstein_scalar_dynamics_claimed": False,
            "covariant_matter_identity_tested": True,
            "genuine_nonzero_curvature_test_executed": True,
            "curvature_test_claimed": True,
            "source_admissibility_claimed": False,
            "bianchi_compatibility_claimed": False,
            "qft_gr_seam_admissibility_claimed": False,
            "qft_gr_seam_closure_claimed": False,
            "quantum_stress_energy_source_claimed": False,
            "multi_background_robustness_claimed": False,
            "higher_dimensional_robustness_claimed": False,
            "pillar_completion_claimed": False,
            "ccft_resumed": False,
            "ccft_validated": False,
            "master_action_promoted": False,
        },
        "recommended_post_review_target": (
            "prepare_scalar_stress_energy_covariant_divergence_identity_"
            "structurally_distinct_curved_background_guardrail_packet"
        ),
        "result_review": {"status": "pending", "target": next_target},
    }


def build_manifest(
    *,
    output_path: Path,
    captured_at_utc: str = CAPTURED_AT_UTC,
) -> dict[str, Any]:
    guardrail_path = REPO_ROOT / GUARDRAIL_RELATIVE_PATH
    script_path = REPO_ROOT / SCRIPT_RELATIVE_PATH
    return {
        "schema_id": f"{CALCULATION_ID}-MANIFEST",
        "calculation_id": CALCULATION_ID,
        "captured_at_utc": captured_at_utc,
        "guardrail_path": GUARDRAIL_RELATIVE_PATH,
        "guardrail_sha256": sha256_file(guardrail_path),
        "script_path": SCRIPT_RELATIVE_PATH,
        "script_sha256": sha256_file(script_path),
        "test_path": TEST_RELATIVE_PATH,
        "execution_command": EXECUTION_COMMAND,
        "python_version": platform.python_version(),
        "numpy_version": np.__version__,
        "output_path": OUTPUT_RELATIVE_PATH,
        "output_sha256": sha256_file(output_path),
        "canonical_json_contract": {
            "encoding": "UTF-8 without BOM",
            "newline": "LF",
            "object_keys": "sorted",
            "separators": [",", ":"],
            "ensure_ascii": True,
            "allow_nan": False,
            "array_order": "preserved",
            "trailing_newline": "exactly one LF",
        },
        "background_geometry_classification": (
            BACKGROUND_GEOMETRY_CLASSIFICATION
        ),
        "scalar_curvature_expected": EXPECTED_SCALAR_CURVATURE,
        "scalar_curvature_measured": EXPECTED_SCALAR_CURVATURE,
        "curvature_test_claimed": True,
        "covariant_matter_identity_tested": True,
        "gravity_evolved": False,
        "einstein_tensor_source_tested": False,
        "two_dimensional_einstein_gravity_degenerate": True,
        "claim_label": "E-REPRO",
        "claim_scope": (
            "Level 3 fixed 1+1 de Sitter scalar matter-identity calculation only"
        ),
        "result_review_status": "pending",
        "result_review_target": RESULT_REVIEW_TARGET,
        "equation_compendium_status": (
            "existing_scoped_e_repro_surface_not_upgraded_by_execution"
        ),
    }


def write_artifacts(
    *,
    output_path: Path,
    manifest_path: Path,
    captured_at_utc: str = CAPTURED_AT_UTC,
) -> tuple[dict[str, Any], dict[str, Any]]:
    result = build_result(captured_at_utc=captured_at_utc)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_bytes(canonical_json_bytes(result))
    manifest = build_manifest(
        output_path=output_path,
        captured_at_utc=captured_at_utc,
    )
    manifest["scalar_curvature_measured"] = result["scalar_curvature_measured"]
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_path.write_bytes(canonical_json_bytes(manifest))
    return result, manifest


def _resolve(path: Path) -> Path:
    return path if path.is_absolute() else REPO_ROOT / path


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Execute the fixed nonzero-curvature 1+1 de Sitter scalar "
            "covariant-divergence calculation."
        )
    )
    parser.add_argument("--output", type=Path, default=Path(OUTPUT_RELATIVE_PATH))
    parser.add_argument(
        "--manifest", type=Path, default=Path(MANIFEST_RELATIVE_PATH)
    )
    parser.add_argument("--captured-at-utc", default=CAPTURED_AT_UTC)
    args = parser.parse_args(argv)
    output_path = _resolve(args.output)
    manifest_path = _resolve(args.manifest)
    result, manifest = write_artifacts(
        output_path=output_path,
        manifest_path=manifest_path,
        captured_at_utc=args.captured_at_utc,
    )
    print(
        json.dumps(
            {
                "calculation_id": CALCULATION_ID,
                "background_geometry_classification": (
                    result["background_geometry_classification"]
                ),
                "scalar_curvature_measured": result[
                    "scalar_curvature_measured"
                ],
                "all_thresholds_passed": result["all_thresholds_passed"],
                "claim_label": result["claim"]["primary_label"],
                "output": OUTPUT_RELATIVE_PATH,
                "output_sha256": manifest["output_sha256"],
                "manifest": MANIFEST_RELATIVE_PATH,
                "result_review_target": result["result_review"]["target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if result["all_thresholds_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
