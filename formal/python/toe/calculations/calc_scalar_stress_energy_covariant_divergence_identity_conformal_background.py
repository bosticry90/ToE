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
    "CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-IDENTITY-"
    "CONFORMAL-BACKGROUND-v0"
)
CAPTURED_AT_UTC = "2026-07-09T00:00:00Z"
GUARDRAIL_RELATIVE_PATH = (
    "formal/docs/release/BOUNDED_CURVED_SPACE_SCALAR_QFT_GR_SOURCE_CONTRACT_"
    "RETEST_GUARDRAIL_PACKET_20260709_v0.json"
)
SCRIPT_RELATIVE_PATH = (
    "formal/python/toe/calculations/"
    "calc_scalar_stress_energy_covariant_divergence_identity_"
    "conformal_background.py"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/calculations/"
    "test_calc_scalar_stress_energy_covariant_divergence_identity_"
    "conformal_background.py"
)
OUTPUT_RELATIVE_PATH = (
    "formal/output/CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-IDENTITY-"
    "CONFORMAL-BACKGROUND-v0.json"
)
MANIFEST_RELATIVE_PATH = (
    "formal/output/CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-IDENTITY-"
    "CONFORMAL-BACKGROUND-MANIFEST-v0.json"
)
RESULT_REVIEW_TARGET = (
    "review_calc_scalar_stress_energy_covariant_divergence_identity_"
    "conformal_background_v0_result"
)
THRESHOLD_REPAIR_TARGET = (
    "repair_calc_scalar_stress_energy_covariant_divergence_identity_"
    "conformal_background_v0_threshold_failure"
)
EXECUTION_COMMAND = (
    "python -m formal.python.toe.calculations."
    "calc_scalar_stress_energy_covariant_divergence_identity_"
    "conformal_background"
)

AMPLITUDE = 0.2
WAVE_NUMBER = 2.0
MASS = 0.0
CONFORMAL_RATE = 0.2
TIME_SLICES = (0.0, 0.37, 0.91)
RESOLUTIONS = (64, 128, 256, 512)
OMEGA_ON = 2.0
OMEGA_OFF = 2.2
EXACT_OFF_SHELL_COEFFICIENT = 0.84
RELATIVE_ERROR_FLOOR = 1e-14

MINIMUM_CONVERGENCE_ORDER = 1.8
MAXIMUM_FINEST_OFF_SHELL_RELATIVE_ERROR = 0.02
MAXIMUM_COEFFICIENT_ERROR = 1e-12
MINIMUM_OFF_TO_ON_DIVERGENCE_RATIO = 100.0
MAXIMUM_METRIC_COMPATIBILITY_ERROR = 1e-12
MAXIMUM_FLAT_LIMIT_DISCREPANCY = 1e-12

PROPOSED_EQUATION_ID = (
    "EQ-QFT-SCALAR-COVARIANT-STRESS-DIVERGENCE-IDENTITY-v0"
)


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


def combined_rms(component_0: np.ndarray, component_1: np.ndarray) -> float:
    return float(np.sqrt(np.mean(np.square(component_0) + np.square(component_1))))


def _metric_and_connection(
    *,
    time: float,
    conformal_rate: float,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, float]:
    scale_factor = math.exp(conformal_rate * time)
    scale_squared = scale_factor**2
    metric = np.array([[-scale_squared, 0.0], [0.0, scale_squared]])
    inverse_metric = np.array(
        [[-1.0 / scale_squared, 0.0], [0.0, 1.0 / scale_squared]]
    )
    gamma = np.zeros((2, 2, 2), dtype=np.float64)
    gamma[0, 0, 0] = conformal_rate
    gamma[0, 1, 1] = conformal_rate
    gamma[1, 0, 1] = conformal_rate
    gamma[1, 1, 0] = conformal_rate
    return metric, inverse_metric, gamma, scale_factor


def metric_compatibility_max_error(
    *,
    time: float,
    conformal_rate: float,
) -> float:
    metric, _, gamma, _ = _metric_and_connection(
        time=time,
        conformal_rate=conformal_rate,
    )
    partial_metric = np.zeros((2, 2, 2), dtype=np.float64)
    partial_metric[0, 0, 0] = 2.0 * conformal_rate * metric[0, 0]
    partial_metric[0, 1, 1] = 2.0 * conformal_rate * metric[1, 1]
    covariant_derivative = np.zeros((2, 2, 2), dtype=np.float64)
    for derivative_index in range(2):
        for mu in range(2):
            for nu in range(2):
                value = partial_metric[derivative_index, mu, nu]
                for rho in range(2):
                    value -= gamma[rho, derivative_index, mu] * metric[rho, nu]
                    value -= gamma[rho, derivative_index, nu] * metric[mu, rho]
                covariant_derivative[derivative_index, mu, nu] = value
    return float(np.max(np.abs(covariant_derivative)))


def _riemann_tensor_for_constant_conformal_rate(conformal_rate: float) -> np.ndarray:
    gamma = _metric_and_connection(time=0.0, conformal_rate=conformal_rate)[2]
    riemann = np.zeros((2, 2, 2, 2), dtype=np.float64)
    for rho in range(2):
        for sigma in range(2):
            for mu in range(2):
                for nu in range(2):
                    value = 0.0
                    for lam in range(2):
                        value += gamma[rho, mu, lam] * gamma[lam, nu, sigma]
                        value -= gamma[rho, nu, lam] * gamma[lam, mu, sigma]
                    riemann[rho, sigma, mu, nu] = value
    return riemann


def geometry_diagnostics() -> dict[str, Any]:
    riemann = _riemann_tensor_for_constant_conformal_rate(CONFORMAL_RATE)
    return {
        "background_geometry_classification": (
            "locally_flat_nontrivial_conformal_connection"
        ),
        "sigma_definition": "sigma(eta) = ln(a(eta)) = 0.2 * eta",
        "sigma_second_derivative": 0.0,
        "scalar_curvature": 0.0,
        "riemann_tensor_max_absolute_component": float(np.max(np.abs(riemann))),
        "nonzero_connection_component_count": 4,
        "curvature_test_claimed": False,
        "covariant_connection_test_claimed": True,
    }


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
    phi_eta_eta = -(omega**2) * phi
    phi_x_eta = AMPLITUDE * WAVE_NUMBER * omega * np.cos(theta)
    return {
        "phi": phi,
        "phi_eta": phi_eta,
        "phi_x": phi_x,
        "phi_eta_eta": phi_eta_eta,
        "phi_x_eta": phi_x_eta,
    }


def evaluate_time_slice(
    *,
    resolution: int,
    time: float,
    omega: float,
    conformal_rate: float = CONFORMAL_RATE,
) -> dict[str, Any]:
    dx = 2.0 * math.pi / resolution
    x = np.arange(resolution, dtype=np.float64) * dx
    fields = _plane_wave_fields(x, time=time, omega=omega)
    phi = fields["phi"]
    phi_eta = fields["phi_eta"]
    phi_x = fields["phi_x"]
    phi_eta_eta = fields["phi_eta_eta"]
    phi_x_eta = fields["phi_x_eta"]
    _, inverse_metric, gamma, scale_factor = _metric_and_connection(
        time=time,
        conformal_rate=conformal_rate,
    )
    inverse_scale_squared = scale_factor**-2
    inverse_scale_fourth = scale_factor**-4

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
        -4.0 * conformal_rate * sum_squares
        + 2.0 * phi_eta * phi_eta_eta
        + 2.0 * phi_x * phi_x_eta
    )
    dt_t01 = inverse_scale_fourth * (
        4.0 * conformal_rate * phi_eta * phi_x
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

    connection_trace_term = np.zeros((2, resolution), dtype=np.float64)
    connection_tensor_term = np.zeros((2, resolution), dtype=np.float64)
    for nu in range(2):
        for mu in range(2):
            for lam in range(2):
                connection_trace_term[nu] += (
                    gamma[mu, mu, lam] * stress[lam, nu]
                )
                connection_tensor_term[nu] += gamma[nu, mu, lam] * stress[mu, lam]
    connection_terms = connection_trace_term + connection_tensor_term
    covariant_divergence = partial_divergence + connection_terms

    coefficient = omega**2 - WAVE_NUMBER**2
    e_phi = inverse_scale_squared * coefficient * phi
    rhs_eta = e_phi * raised_eta
    rhs_x = e_phi * raised_x
    rhs = np.stack([rhs_eta, rhs_x])
    covariant_error = covariant_divergence - rhs
    naive_partial_error = partial_divergence - rhs

    rhs_norm_eta = rms(rhs_eta)
    rhs_norm_x = rms(rhs_x)
    rhs_combined_norm = combined_rms(rhs_eta, rhs_x)
    covariant_error_eta = rms(covariant_error[0])
    covariant_error_x = rms(covariant_error[1])
    covariant_error_combined = combined_rms(
        covariant_error[0],
        covariant_error[1],
    )

    return {
        "resolution_N": resolution,
        "time_eta": time,
        "dx": dx,
        "scale_factor": scale_factor,
        "equation_residual_coefficient_before_a_inverse_squared": coefficient,
        "covariant_divergence_norms": {
            "nu_eta": rms(covariant_divergence[0]),
            "nu_x": rms(covariant_divergence[1]),
            "combined": combined_rms(covariant_divergence[0], covariant_divergence[1]),
        },
        "rhs_norms": {
            "nu_eta": rhs_norm_eta,
            "nu_x": rhs_norm_x,
            "combined": rhs_combined_norm,
        },
        "covariant_identity_absolute_error_norms": {
            "nu_eta": covariant_error_eta,
            "nu_x": covariant_error_x,
            "combined": covariant_error_combined,
        },
        "covariant_identity_relative_error_norms": {
            "nu_eta": covariant_error_eta
            / max(rhs_norm_eta, RELATIVE_ERROR_FLOOR),
            "nu_x": covariant_error_x / max(rhs_norm_x, RELATIVE_ERROR_FLOOR),
            "combined": covariant_error_combined
            / max(rhs_combined_norm, RELATIVE_ERROR_FLOOR),
        },
        "connection_term_norms": {
            "nu_eta": rms(connection_terms[0]),
            "nu_x": rms(connection_terms[1]),
            "combined": combined_rms(connection_terms[0], connection_terms[1]),
        },
        "naive_partial_divergence_diagnostic": {
            "identity_error_norm_nu_eta": rms(naive_partial_error[0]),
            "identity_error_norm_nu_x": rms(naive_partial_error[1]),
            "identity_error_norm_combined": combined_rms(
                naive_partial_error[0],
                naive_partial_error[1],
            ),
            "diagnostic_only_not_guardrail_threshold": True,
        },
        "metric_compatibility_max_absolute_error": metric_compatibility_max_error(
            time=time,
            conformal_rate=conformal_rate,
        ),
        "_arrays": {
            "stress": stress,
            "partial_divergence": partial_divergence,
            "connection_terms": connection_terms,
            "covariant_divergence": covariant_divergence,
            "rhs": rhs,
            "covariant_error": covariant_error,
            "naive_partial_error": naive_partial_error,
            "e_phi": e_phi,
            "exact_reference": (
                EXACT_OFF_SHELL_COEFFICIENT * inverse_scale_squared * phi
            ),
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
    dt_t00 = phi_eta * phi_eta_eta + phi_x * phi_x_eta
    dt_t01 = -(phi_eta_eta * phi_x + phi_eta * phi_x_eta)
    divergence = np.stack(
        [
            dt_t00 + centered_periodic_difference(stress_01, dx),
            dt_t01 + centered_periodic_difference(stress_11, dx),
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
                    conformal_rate=0.0,
                )["_arrays"]
                direct = _evaluate_flat_reference(
                    resolution=resolution,
                    time=time,
                    omega=omega,
                )
                discrepancies.append(
                    float(
                        np.max(
                            np.abs(covariant["covariant_divergence"] - direct["divergence"])
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
        evaluate_time_slice(resolution=resolution, time=time, omega=omega)
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
    naive_eta = concatenate("naive_partial_error", 0)
    naive_x = concatenate("naive_partial_error", 1)
    e_phi = concatenate("e_phi")
    exact_reference = concatenate("exact_reference")

    rhs_eta_norm = rms(rhs_eta)
    rhs_x_norm = rms(rhs_x)
    rhs_combined_norm = combined_rms(rhs_eta, rhs_x)
    error_eta_norm = rms(error_eta)
    error_x_norm = rms(error_x)
    error_combined_norm = combined_rms(error_eta, error_x)
    naive_combined_norm = combined_rms(naive_eta, naive_x)
    return {
        "resolution_N": resolution,
        "time_slice_count": len(TIME_SLICES),
        "covariant_divergence_norms": {
            "nu_eta": rms(divergence_eta),
            "nu_x": rms(divergence_x),
            "combined": combined_rms(divergence_eta, divergence_x),
        },
        "rhs_norms": {
            "nu_eta": rhs_eta_norm,
            "nu_x": rhs_x_norm,
            "combined": rhs_combined_norm,
        },
        "covariant_identity_absolute_error_norms": {
            "nu_eta": error_eta_norm,
            "nu_x": error_x_norm,
            "combined": error_combined_norm,
        },
        "covariant_identity_relative_error_norms": {
            "nu_eta": error_eta_norm / max(rhs_eta_norm, RELATIVE_ERROR_FLOOR),
            "nu_x": error_x_norm / max(rhs_x_norm, RELATIVE_ERROR_FLOOR),
            "combined": error_combined_norm
            / max(rhs_combined_norm, RELATIVE_ERROR_FLOOR),
        },
        "naive_partial_divergence_diagnostic": {
            "identity_error_norm_nu_eta": rms(naive_eta),
            "identity_error_norm_nu_x": rms(naive_x),
            "identity_error_norm_combined": naive_combined_norm,
            "naive_to_covariant_identity_error_ratio": naive_combined_norm
            / max(error_combined_norm, RELATIVE_ERROR_FLOOR),
            "diagnostic_only_not_guardrail_threshold": True,
        },
        "exact_residual_reference": {
            "expected_coefficient_before_a_inverse_squared": (
                EXACT_OFF_SHELL_COEFFICIENT
            ),
            "computed_coefficient_before_a_inverse_squared": (
                omega**2 - WAVE_NUMBER**2
            ),
            "coefficient_absolute_error": abs(
                omega**2 - WAVE_NUMBER**2 - EXACT_OFF_SHELL_COEFFICIENT
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
            off_to_on_ratio > MINIMUM_OFF_TO_ON_DIVERGENCE_RATIO
        ),
        "metric_compatibility_error_at_most_1e_12": (
            metric_error <= MAXIMUM_METRIC_COMPATIBILITY_ERROR
        ),
        "flat_limit_discrepancy_at_most_1e_12": (
            flat_discrepancy <= MAXIMUM_FLAT_LIMIT_DISCREPANCY
        ),
    }
    passed = all(checks.values())
    claim_label = "E-REPRO" if passed else "B-BLOCKED"
    next_target = RESULT_REVIEW_TARGET if passed else THRESHOLD_REPAIR_TARGET
    naive_ratio = finest_on["naive_partial_divergence_diagnostic"][
        "naive_to_covariant_identity_error_ratio"
    ]

    return {
        "schema_id": f"{CALCULATION_ID}-RESULT",
        "calculation_id": CALCULATION_ID,
        "calculation_status": (
            "executed_pending_result_review" if passed else "executed_blocked"
        ),
        "captured_at_utc": captured_at_utc,
        "question": (
            "Numerically test the scalar covariant stress-energy divergence "
            "identity in nontrivial conformal coordinates on locally flat "
            "1+1-dimensional spacetime."
        ),
        "background_geometry": geometry_diagnostics(),
        "interpretation": {
            "successful_result_establishes": (
                "covariant-divergence identity reproduced in a nontrivial "
                "conformal-coordinate representation of locally flat spacetime"
            ),
            "successful_result_does_not_establish": (
                "stress-energy behavior under genuine nonzero spacetime curvature"
            ),
        },
        "mathematical_convention": {
            "metric": "g_mu_nu = a(eta)^2 diag(-1,+1)",
            "scale_factor": "a(eta) = exp(0.2 eta)",
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
            "conformal_rate_H": CONFORMAL_RATE,
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
            "relative_error_floor": RELATIVE_ERROR_FLOOR,
        },
        "on_shell": {
            "control_role": "positive covariant-conservation control",
            "relative_error_against_zero_formed": False,
            "resolution_aggregates": on_aggregates,
            "time_slice_results": on_rows,
            "combined_absolute_divergence_convergence_orders": on_orders,
        },
        "off_shell": {
            "control_role": "negative field-equation residual control",
            "exact_reference": "E_phi = 0.84 * a(eta)^(-2) * phi",
            "resolution_aggregates": off_aggregates,
            "time_slice_results": off_rows,
            "combined_identity_error_convergence_orders": off_orders,
        },
        "naive_partial_divergence_negative_control": {
            "description": (
                "replace nabla_mu T^{mu nu} by partial_mu T^{mu nu} and retain "
                "the same right-hand side"
            ),
            "expected": "generally fails when connection terms are omitted",
            "finest_on_shell_naive_to_covariant_error_ratio": naive_ratio,
            "failure_detected": naive_ratio > 100.0,
            "diagnostic_only_not_guardrail_threshold": True,
        },
        "thresholds": {
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
        },
        "threshold_evidence": {
            "minimum_observed_two_finest_convergence_order": (
                minimum_two_finest_order
            ),
            "finest_combined_off_shell_relative_error": finest_off_relative_error,
            "exact_coefficient_absolute_error": coefficient_error,
            "finest_off_to_on_divergence_norm_ratio": off_to_on_ratio,
            "metric_compatibility_max_absolute_error": metric_error,
            "flat_limit_max_absolute_discrepancy": flat_discrepancy,
        },
        "threshold_checks": checks,
        "all_thresholds_passed": passed,
        "claim": {
            "primary_label": claim_label,
            "claim_status": (
                "generated_pending_result_review"
                if passed
                else "blocked_threshold_failure"
            ),
            "claim_scope": (
                "Level 3 locally-flat conformal-coordinate scalar covariant-"
                "divergence calculation only"
            ),
            "claim_ceiling_level": 3,
            "next_work_status": next_target,
        },
        "proposed_equation_id_pending_review": PROPOSED_EQUATION_ID,
        "equation_compendium_edited": False,
        "boundary": {
            "calculation_executed": True,
            "background_metric_evolved": False,
            "einstein_equation_solved": False,
            "genuine_nonzero_curvature_test_executed": False,
            "curvature_test_claimed": False,
            "covariant_connection_test_claimed": True,
            "source_admissibility_claimed": False,
            "bianchi_compatibility_claimed": False,
            "qft_gr_seam_admissibility_claimed": False,
            "qft_gr_seam_closure_claimed": False,
            "quantum_stress_energy_source_claimed": False,
            "pillar_completion_claimed": False,
            "ccft_resumed": False,
            "ccft_validated": False,
            "master_action_promoted": False,
        },
        "recommended_post_review_target": (
            "execute_calc_scalar_stress_energy_covariant_divergence_identity_"
            "nonzero_curvature_background_v0"
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
            "locally_flat_nontrivial_conformal_connection"
        ),
        "scalar_curvature": 0.0,
        "curvature_test_claimed": False,
        "covariant_connection_test_claimed": True,
        "claim_label": "E-REPRO",
        "claim_scope": (
            "Level 3 locally-flat conformal-coordinate covariance calculation only"
        ),
        "result_review_status": "pending",
        "result_review_target": RESULT_REVIEW_TARGET,
        "equation_compendium_status": "proposed_pending_result_review",
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
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_path.write_bytes(canonical_json_bytes(manifest))
    return result, manifest


def _resolve(path: Path) -> Path:
    return path if path.is_absolute() else REPO_ROOT / path


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Execute the locally-flat conformal covariance pretest."
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
                "background_geometry_classification": result[
                    "background_geometry"
                ]["background_geometry_classification"],
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
