from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
import sys
from pathlib import Path
from typing import Any

import numpy as np

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
CALCULATION_ID = (
    "CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-IDENTITY-HIGHER-"
    "DIMENSIONAL-CURVED-BACKGROUND-v0"
)
CAPTURED_AT_UTC = "2026-07-09T00:00:00Z"
GUARDRAIL_REVISED_AT_UTC = "2026-07-10T00:00:00Z"
GUARDRAIL_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_"
    "HIGHER_DIMENSIONAL_CURVED_BACKGROUND_GUARDRAIL_PACKET_20260709_v1.json"
)
SCRIPT_RELATIVE_PATH = (
    "formal/python/toe/calculations/"
    "calc_scalar_stress_energy_covariant_divergence_identity_higher_"
    "dimensional_curved_background.py"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/calculations/"
    "test_calc_scalar_stress_energy_covariant_divergence_identity_higher_"
    "dimensional_curved_background.py"
)
OUTPUT_RELATIVE_PATH = (
    "formal/output/CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-IDENTITY-"
    "HIGHER-DIMENSIONAL-CURVED-BACKGROUND-v0.json"
)
MANIFEST_RELATIVE_PATH = (
    "formal/output/CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-IDENTITY-"
    "HIGHER-DIMENSIONAL-CURVED-BACKGROUND-MANIFEST-v0.json"
)
EXECUTION_REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_"
    "HIGHER_DIMENSIONAL_CURVED_BACKGROUND_CALCULATION_EXECUTION_20260709_v0.json"
)
RESULT_REVIEW_TARGET = (
    "review_calc_scalar_stress_energy_covariant_divergence_identity_higher_"
    "dimensional_curved_background_v0_result"
)
THRESHOLD_FAILURE_TARGET = (
    "diagnose_calc_scalar_stress_energy_covariant_divergence_identity_higher_"
    "dimensional_curved_background_v0_threshold_failure"
)
DIAGNOSTIC_FAILURE_TARGET = THRESHOLD_FAILURE_TARGET
EXECUTION_COMMAND = (
    "python -m formal.python.toe.calculations."
    "calc_scalar_stress_energy_covariant_divergence_identity_higher_"
    "dimensional_curved_background"
)

BACKGROUND_GEOMETRY_CLASSIFICATION = (
    "fixed_nonzero_spatially_varying_curvature_2plus1_warped_periodic_"
    "background"
)
EQUATION_ID = "EQ-QFT-SCALAR-COVARIANT-STRESS-DIVERGENCE-IDENTITY-v0"

AMPLITUDE = 0.2
MASS = 1.0
WARP_AMPLITUDE = 0.2
X_WAVE_NUMBER = 2.0
Y_WAVE_NUMBER = 2.0
X_OMEGA = 1.7
Y_OMEGA = 1.5
TIME_SLICES = (0.0, 0.37, 0.91)
RESOLUTIONS = (32, 64, 128, 256)
SPATIAL_RESOLUTIONS = RESOLUTIONS
PROFILE_IDS = ("on_shell_temporal_mode", "off_shell_x_mode", "off_shell_y_mode")
COMPONENT_LABELS = ("nu_t", "nu_x", "nu_y")
COORDINATE_GRID_NORM_NAME = "coordinate_grid_euclidean_component_rms"

EPSILON_R = 1e-12
EPSILON_NORM = 1e-14
EPSILON_CONTROL = 1e-14

MINIMUM_CONVERGENCE_ORDER = 1.8
MAXIMUM_FINEST_RELATIVE_ERROR = 0.02
MAXIMUM_ON_SHELL_DIVERGENCE = 1e-11
MAXIMUM_ANALYTIC_REFERENCE_ERROR = 1e-12
MAXIMUM_METRIC_COMPATIBILITY_ERROR = 1e-12
MAXIMUM_CURVATURE_ROUTE_ERROR = 1e-12
MINIMUM_PEAK_ABSOLUTE_CURVATURE = 0.49
MINIMUM_CURVATURE_VARIATION = 0.8
MAXIMUM_FLAT_LIMIT_ERROR = 1e-11
MINIMUM_CONNECTION_CONTROL_RATIO = 10.0
MINIMUM_GEOMETRY_DEFECT_DISCREPANCY = 0.02


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


def load_guardrail() -> tuple[dict[str, Any], str]:
    """Load the immutable v1 contract and hash its current bytes.

    The hash is deliberately not copied into this source file.  The manifest
    binds the exact guardrail bytes consumed by each execution.
    """

    path = REPO_ROOT / GUARDRAIL_RELATIVE_PATH
    payload = json.loads(path.read_text(encoding="utf-8"))
    return payload, sha256_file(path)


def centered_periodic_difference(
    values: np.ndarray,
    spacing: float,
    *,
    axis: int,
) -> np.ndarray:
    return (
        np.roll(values, -1, axis=axis) - np.roll(values, 1, axis=axis)
    ) / (2.0 * spacing)


def rms(values: np.ndarray) -> float:
    return float(np.sqrt(np.mean(np.square(values))))


def component_rms(values: np.ndarray) -> dict[str, float]:
    return {
        label: rms(values[index])
        for index, label in enumerate(COMPONENT_LABELS)
    }


def combined_rms(values: np.ndarray) -> float:
    return float(np.sqrt(np.mean(np.sum(np.square(values), axis=0))))


def _geometry_arrays(
    resolution: int,
    *,
    warp_amplitude: float = WARP_AMPLITUDE,
) -> dict[str, np.ndarray | float]:
    dx = 2.0 * math.pi / resolution
    x = np.arange(resolution, dtype=np.float64) * dx
    f = 1.0 + warp_amplitude * np.cos(x)
    fp = -warp_amplitude * np.sin(x)
    fpp = -warp_amplitude * np.cos(x)
    metric = np.zeros((3, 3, resolution), dtype=np.float64)
    inverse_metric = np.zeros_like(metric)
    metric[0, 0] = -1.0
    metric[1, 1] = 1.0
    metric[2, 2] = f**2
    inverse_metric[0, 0] = -1.0
    inverse_metric[1, 1] = 1.0
    inverse_metric[2, 2] = f**-2
    metric_derivative = np.zeros((3, 3, 3, resolution), dtype=np.float64)
    metric_derivative[1, 2, 2] = 2.0 * f * fp
    metric_second_derivative = np.zeros(
        (3, 3, 3, 3, resolution), dtype=np.float64
    )
    metric_second_derivative[1, 1, 2, 2] = 2.0 * (fp**2 + f * fpp)
    return {
        "dx": dx,
        "x": x,
        "f": f,
        "fp": fp,
        "fpp": fpp,
        "metric": metric,
        "inverse_metric": inverse_metric,
        "metric_derivative": metric_derivative,
        "metric_second_derivative": metric_second_derivative,
    }


def _connection_and_derivative_from_metric(
    *,
    inverse_metric: np.ndarray,
    metric_derivative: np.ndarray,
    metric_second_derivative: np.ndarray,
) -> tuple[np.ndarray, np.ndarray]:
    resolution = inverse_metric.shape[-1]
    gamma = np.zeros((3, 3, 3, resolution), dtype=np.float64)
    for rho in range(3):
        for mu in range(3):
            for nu in range(3):
                for sigma in range(3):
                    gamma[rho, mu, nu] += 0.5 * inverse_metric[rho, sigma] * (
                        metric_derivative[mu, sigma, nu]
                        + metric_derivative[nu, sigma, mu]
                        - metric_derivative[sigma, mu, nu]
                    )

    inverse_derivative = np.zeros((3, 3, 3, resolution), dtype=np.float64)
    for kappa in range(3):
        for rho in range(3):
            for sigma in range(3):
                for alpha in range(3):
                    for beta in range(3):
                        inverse_derivative[kappa, rho, sigma] -= (
                            inverse_metric[rho, alpha]
                            * metric_derivative[kappa, alpha, beta]
                            * inverse_metric[beta, sigma]
                        )

    gamma_derivative = np.zeros((3, 3, 3, 3, resolution), dtype=np.float64)
    for kappa in range(3):
        for rho in range(3):
            for mu in range(3):
                for nu in range(3):
                    for sigma in range(3):
                        first = (
                            metric_derivative[mu, sigma, nu]
                            + metric_derivative[nu, sigma, mu]
                            - metric_derivative[sigma, mu, nu]
                        )
                        second = (
                            metric_second_derivative[kappa, mu, sigma, nu]
                            + metric_second_derivative[kappa, nu, sigma, mu]
                            - metric_second_derivative[kappa, sigma, mu, nu]
                        )
                        gamma_derivative[kappa, rho, mu, nu] += 0.5 * (
                            inverse_derivative[kappa, rho, sigma] * first
                            + inverse_metric[rho, sigma] * second
                        )
    return gamma, gamma_derivative


def reconstruct_curvature(
    resolution: int,
    *,
    warp_amplitude: float = WARP_AMPLITUDE,
) -> dict[str, Any]:
    """Generic metric-to-curvature reconstruction, without analytic shortcut."""

    geometry = _geometry_arrays(resolution, warp_amplitude=warp_amplitude)
    inverse_metric = geometry["inverse_metric"]
    assert isinstance(inverse_metric, np.ndarray)
    gamma, gamma_derivative = _connection_and_derivative_from_metric(
        inverse_metric=inverse_metric,
        metric_derivative=geometry["metric_derivative"],
        metric_second_derivative=geometry["metric_second_derivative"],
    )
    riemann = np.zeros((3, 3, 3, 3, resolution), dtype=np.float64)
    for rho in range(3):
        for sigma in range(3):
            for mu in range(3):
                for nu in range(3):
                    value = (
                        gamma_derivative[mu, rho, nu, sigma]
                        - gamma_derivative[nu, rho, mu, sigma]
                    )
                    for lam in range(3):
                        value = value + (
                            gamma[rho, mu, lam] * gamma[lam, nu, sigma]
                            - gamma[rho, nu, lam] * gamma[lam, mu, sigma]
                        )
                    riemann[rho, sigma, mu, nu] = value
    ricci = np.zeros((3, 3, resolution), dtype=np.float64)
    for sigma in range(3):
        for nu in range(3):
            for rho in range(3):
                ricci[sigma, nu] += riemann[rho, sigma, rho, nu]
    scalar = np.zeros(resolution, dtype=np.float64)
    for sigma in range(3):
        for nu in range(3):
            scalar += inverse_metric[sigma, nu] * ricci[sigma, nu]
    return {
        "scalar_curvature": scalar,
        "ricci_tensor": ricci,
        "connection": gamma,
        "riemann_tensor_max_absolute_component": float(np.max(np.abs(riemann))),
    }


def analytic_scalar_curvature(
    x: np.ndarray,
    *,
    warp_amplitude: float = WARP_AMPLITUDE,
) -> np.ndarray:
    f = 1.0 + warp_amplitude * np.cos(x)
    fpp = -warp_amplitude * np.cos(x)
    return -2.0 * fpp / f


def metric_compatibility_max_error(
    resolution: int,
    *,
    warp_amplitude: float = WARP_AMPLITUDE,
) -> float:
    geometry = _geometry_arrays(resolution, warp_amplitude=warp_amplitude)
    metric = geometry["metric"]
    inverse_metric = geometry["inverse_metric"]
    derivative = geometry["metric_derivative"]
    gamma = _connection_and_derivative_from_metric(
        inverse_metric=inverse_metric,
        metric_derivative=derivative,
        metric_second_derivative=geometry["metric_second_derivative"],
    )[0]
    covariant_derivative = np.array(derivative, copy=True)
    for kappa in range(3):
        for mu in range(3):
            for nu in range(3):
                for rho in range(3):
                    covariant_derivative[kappa, mu, nu] -= (
                        gamma[rho, kappa, mu] * metric[rho, nu]
                        + gamma[rho, kappa, nu] * metric[mu, rho]
                    )
    return float(np.max(np.abs(covariant_derivative)))


def geometry_safety_verification() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for resolution in RESOLUTIONS:
        geometry = _geometry_arrays(resolution)
        f = geometry["f"]
        determinant = -(f**2)
        rows.append(
            {
                "resolution_N": resolution,
                "minimum_warp_factor": float(np.min(f)),
                "maximum_warp_factor": float(np.max(f)),
                "maximum_inverse_y_metric_factor": float(np.max(f**-2)),
                "minimum_absolute_determinant": float(
                    np.min(np.abs(determinant))
                ),
                "nonsingular": bool(np.all(f > 0.0)),
            }
        )
    return {
        "rows": rows,
        "minimum_warp_factor": min(row["minimum_warp_factor"] for row in rows),
        "maximum_warp_factor": max(row["maximum_warp_factor"] for row in rows),
        "maximum_inverse_y_metric_factor": max(
            row["maximum_inverse_y_metric_factor"] for row in rows
        ),
        "minimum_absolute_determinant": min(
            row["minimum_absolute_determinant"] for row in rows
        ),
        "all_frozen_grids_nonsingular": all(row["nonsingular"] for row in rows),
    }


def curvature_verification() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    maximum_route_error = 0.0
    maximum_metric_error = 0.0
    maximum_connection_error = 0.0
    maximum_ricci_error = 0.0
    all_analytic_values: list[np.ndarray] = []
    for resolution in RESOLUTIONS:
        geometry = _geometry_arrays(resolution)
        x = geometry["x"]
        analytic = analytic_scalar_curvature(x)
        reconstruction = reconstruct_curvature(resolution)
        generic = reconstruction["scalar_curvature"]
        f = geometry["f"]
        fp = geometry["fp"]
        fpp = geometry["fpp"]
        expected_gamma = np.zeros_like(reconstruction["connection"])
        expected_gamma[1, 2, 2] = -f * fp
        expected_gamma[2, 1, 2] = fp / f
        expected_gamma[2, 2, 1] = fp / f
        connection_error = float(
            np.max(np.abs(reconstruction["connection"] - expected_gamma))
        )
        expected_ricci = np.zeros_like(reconstruction["ricci_tensor"])
        expected_ricci[1, 1] = -fpp / f
        expected_ricci[2, 2] = -f * fpp
        ricci_error = float(
            np.max(np.abs(reconstruction["ricci_tensor"] - expected_ricci))
        )
        absolute_error = np.abs(generic - analytic)
        included = np.abs(analytic) > EPSILON_R
        excluded_indices = np.flatnonzero(~included).astype(int).tolist()
        relative = np.abs(generic[included] - analytic[included]) / np.abs(
            analytic[included]
        )
        metric_error = metric_compatibility_max_error(resolution)
        maximum_route_error = max(maximum_route_error, float(np.max(absolute_error)))
        maximum_metric_error = max(maximum_metric_error, metric_error)
        maximum_connection_error = max(maximum_connection_error, connection_error)
        maximum_ricci_error = max(maximum_ricci_error, ricci_error)
        all_analytic_values.append(analytic)
        point_errors = []
        for index in range(resolution):
            excluded = not bool(included[index])
            point_errors.append(
                {
                    "x_index": index,
                    "absolute_error": float(absolute_error[index]),
                    "relative_error": (
                        None
                        if excluded
                        else float(absolute_error[index] / abs(analytic[index]))
                    ),
                    "status": (
                        "excluded_near_zero" if excluded else "reported"
                    ),
                }
            )
        rows.append(
            {
                "resolution_N": resolution,
                "grid_shape": [resolution, resolution],
                "maximum_absolute_error": float(np.max(absolute_error)),
                "maximum_relative_error_away_from_zero": float(np.max(relative)),
                "relative_error_cutoff_epsilon_R": EPSILON_R,
                "excluded_x_index_count": len(excluded_indices),
                "excluded_x_indices": excluded_indices,
                "excluded_spatial_gridpoint_count": len(excluded_indices)
                * resolution,
                "crossing_locations": [math.pi / 2.0, 3.0 * math.pi / 2.0],
                "excluded_crossing_absolute_errors": [
                    float(absolute_error[index]) for index in excluded_indices
                ],
                "excluded_crossing_relative_errors": [
                    {
                        "x_index": index,
                        "relative_error": None,
                        "status": "excluded_near_zero",
                    }
                    for index in excluded_indices
                ],
                "x_index_error_rows": point_errors,
                "metric_compatibility_max_absolute_error": metric_error,
                "connection_formula_max_absolute_error": connection_error,
                "ricci_formula_max_absolute_error": ricci_error,
            }
        )
    finest = all_analytic_values[-1]
    return {
        "analytic_route": {
            "formula": "R(x) = -2*f''(x)/f(x)",
            "substituted_formula": "R(x) = 0.4*cos(x)/(1+0.2*cos(x))",
        },
        "generic_route": {
            "method": (
                "metric,dg,ddg -> Christoffel,dChristoffel -> Riemann -> "
                "Ricci -> scalar index loops"
            ),
            "analytic_curvature_helper_called": False,
        },
        "resolution_diagnostics": rows,
        "maximum_curvature_route_absolute_discrepancy": maximum_route_error,
        "maximum_metric_compatibility_absolute_error": maximum_metric_error,
        "maximum_connection_formula_absolute_error": maximum_connection_error,
        "maximum_ricci_formula_absolute_error": maximum_ricci_error,
        "nonzero_christoffel_component_formulas": {
            "Gamma^x_yy": "-f*f'",
            "Gamma^y_xy": "f'/f",
            "Gamma^y_yx": "f'/f",
        },
        "structurally_allowed_nonzero_christoffel_component_count": 3,
        "scalar_curvature_minimum": float(np.min(finest)),
        "scalar_curvature_maximum": float(np.max(finest)),
        "peak_absolute_scalar_curvature": float(np.max(np.abs(finest))),
        "peak_to_peak_scalar_curvature": float(np.ptp(finest)),
        "curvature_zero_reporting_is_non_gating": True,
    }


def _profile_fields(
    profile_id: str,
    x: np.ndarray,
    y: np.ndarray,
    *,
    time: float,
) -> dict[str, np.ndarray]:
    shape = x.shape
    zeros = np.zeros(shape, dtype=np.float64)
    if profile_id == "on_shell_temporal_mode":
        phi = np.full(shape, AMPLITUDE * math.cos(MASS * time))
        phi_t = np.full(shape, -AMPLITUDE * MASS * math.sin(MASS * time))
        phi_tt = -(MASS**2) * phi
        return {
            "phi": phi,
            "phi_t": phi_t,
            "phi_x": zeros,
            "phi_y": zeros,
            "phi_tt": phi_tt,
            "phi_tx": zeros,
            "phi_ty": zeros,
            "phi_xx": zeros,
            "phi_yy": zeros,
        }
    if profile_id == "off_shell_x_mode":
        cos_t = math.cos(X_OMEGA * time)
        sin_t = math.sin(X_OMEGA * time)
        cos_x = np.cos(X_WAVE_NUMBER * x)
        sin_x = np.sin(X_WAVE_NUMBER * x)
        phi = AMPLITUDE * cos_t * cos_x
        return {
            "phi": phi,
            "phi_t": -AMPLITUDE * X_OMEGA * sin_t * cos_x,
            "phi_x": -AMPLITUDE * X_WAVE_NUMBER * cos_t * sin_x,
            "phi_y": zeros,
            "phi_tt": -(X_OMEGA**2) * phi,
            "phi_tx": (
                AMPLITUDE * X_OMEGA * X_WAVE_NUMBER * sin_t * sin_x
            ),
            "phi_ty": zeros,
            "phi_xx": -(X_WAVE_NUMBER**2) * phi,
            "phi_yy": zeros,
        }
    if profile_id == "off_shell_y_mode":
        cos_t = math.cos(Y_OMEGA * time)
        sin_t = math.sin(Y_OMEGA * time)
        cos_y = np.cos(Y_WAVE_NUMBER * y)
        sin_y = np.sin(Y_WAVE_NUMBER * y)
        phi = AMPLITUDE * cos_t * cos_y
        return {
            "phi": phi,
            "phi_t": -AMPLITUDE * Y_OMEGA * sin_t * cos_y,
            "phi_x": zeros,
            "phi_y": -AMPLITUDE * Y_WAVE_NUMBER * cos_t * sin_y,
            "phi_tt": -(Y_OMEGA**2) * phi,
            "phi_tx": zeros,
            "phi_ty": (
                AMPLITUDE * Y_OMEGA * Y_WAVE_NUMBER * sin_t * sin_y
            ),
            "phi_xx": zeros,
            "phi_yy": -(Y_WAVE_NUMBER**2) * phi,
        }
    raise ValueError(f"unknown profile_id: {profile_id}")


def _explicit_profile_residual(
    profile_id: str,
    fields: dict[str, np.ndarray],
    *,
    f: np.ndarray,
    fp: np.ndarray,
    time: float,
    wrong_y_inverse_metric: bool = False,
) -> np.ndarray:
    phi = fields["phi"]
    if profile_id == "on_shell_temporal_mode":
        return np.zeros_like(phi)
    if profile_id == "off_shell_x_mode":
        x_factor = np.sin(
            X_WAVE_NUMBER
            * np.arange(phi.shape[0], dtype=np.float64)[:, None]
            * (2.0 * math.pi / phi.shape[0])
        )
        return (
            (X_OMEGA**2 - MASS**2 - X_WAVE_NUMBER**2) * phi
            - AMPLITUDE
            * X_WAVE_NUMBER
            * (fp / f)[:, None]
            * math.cos(X_OMEGA * time)
            * x_factor
        )
    inverse_y = 1.0 if wrong_y_inverse_metric else f[:, None] ** -2
    return (Y_OMEGA**2 - MASS**2 - Y_WAVE_NUMBER**2 * inverse_y) * phi


def _assembled_profile_residual(
    fields: dict[str, np.ndarray],
    *,
    f: np.ndarray,
    fp: np.ndarray,
) -> np.ndarray:
    return (
        -fields["phi_tt"]
        + fields["phi_xx"]
        + (fp / f)[:, None] * fields["phi_x"]
        + f[:, None] ** -2 * fields["phi_yy"]
        - MASS**2 * fields["phi"]
    )


def _stress_and_temporal_divergence_piece(
    fields: dict[str, np.ndarray],
    *,
    f: np.ndarray,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    lower = np.stack([fields["phi_t"], fields["phi_x"], fields["phi_y"]])
    lower_t = np.stack([fields["phi_tt"], fields["phi_tx"], fields["phi_ty"]])
    raised = np.empty_like(lower)
    raised_t = np.empty_like(lower_t)
    raised[0] = -lower[0]
    raised[1] = lower[1]
    raised[2] = f[:, None] ** -2 * lower[2]
    raised_t[0] = -lower_t[0]
    raised_t[1] = lower_t[1]
    raised_t[2] = f[:, None] ** -2 * lower_t[2]
    contraction = np.sum(lower * raised, axis=0)
    lagrangian_bracket = 0.5 * (contraction + MASS**2 * fields["phi"] ** 2)
    bracket_t = np.sum(lower_t * raised, axis=0) + (
        MASS**2 * fields["phi"] * fields["phi_t"]
    )
    stress = np.empty((3, 3, *fields["phi"].shape), dtype=np.float64)
    for mu in range(3):
        for nu in range(3):
            stress[mu, nu] = raised[mu] * raised[nu]
    stress[0, 0] += lagrangian_bracket
    stress[1, 1] -= lagrangian_bracket
    stress[2, 2] -= f[:, None] ** -2 * lagrangian_bracket
    temporal_piece = np.empty((3, *fields["phi"].shape), dtype=np.float64)
    for nu in range(3):
        temporal_piece[nu] = (
            raised_t[0] * raised[nu] + raised[0] * raised_t[nu]
        )
    temporal_piece[0] += bracket_t
    return stress, temporal_piece, raised


def compute_covariant_divergence_slice(
    *,
    resolution: int,
    time: float,
    profile_id: str,
    warp_amplitude: float = WARP_AMPLITUDE,
) -> dict[str, np.ndarray]:
    """Compute divergence without consulting either analytic residual helper."""

    geometry = _geometry_arrays(resolution, warp_amplitude=warp_amplitude)
    spacing = float(geometry["dx"])
    x_1d = geometry["x"]
    x, y = np.meshgrid(x_1d, x_1d, indexing="ij")
    fields = _profile_fields(profile_id, x, y, time=time)
    f = geometry["f"]
    stress, temporal_piece, raised = _stress_and_temporal_divergence_piece(
        fields, f=f
    )
    partial = temporal_piece.copy()
    for nu in range(3):
        partial[nu] += centered_periodic_difference(
            stress[1, nu], spacing, axis=0
        )
        partial[nu] += centered_periodic_difference(
            stress[2, nu], spacing, axis=1
        )
    gamma = _connection_and_derivative_from_metric(
        inverse_metric=geometry["inverse_metric"],
        metric_derivative=geometry["metric_derivative"],
        metric_second_derivative=geometry["metric_second_derivative"],
    )[0]
    volume_trace = np.zeros_like(partial)
    tensor_index = np.zeros_like(partial)
    for nu in range(3):
        for mu in range(3):
            for lam in range(3):
                volume_trace[nu] += (
                    gamma[mu, mu, lam, :, None] * stress[lam, nu]
                )
                tensor_index[nu] += (
                    gamma[nu, mu, lam, :, None] * stress[mu, lam]
                )
    return {
        "divergence": partial + volume_trace + tensor_index,
        "partial_divergence": partial,
        "volume_trace_connection_term": volume_trace,
        "tensor_index_connection_term": tensor_index,
        "stress": stress,
        "raised_gradient": raised,
        "f": f,
        "fp": geometry["fp"],
        "fields": fields,
    }


def _metric_bundle(
    values: np.ndarray,
    reference: np.ndarray,
    *,
    exact_zero_components: list[bool] | None = None,
) -> dict[str, Any]:
    error = values - reference
    if exact_zero_components is None:
        exact_zero_components = [
            not bool(np.any(reference[index] != 0.0)) for index in range(3)
        ]
    components: dict[str, Any] = {}
    for index, label in enumerate(COMPONENT_LABELS):
        absolute = rms(error[index])
        reference_norm = rms(reference[index])
        exact_zero = exact_zero_components[index]
        components[label] = {
            "value_rms": rms(values[index]),
            "reference_rms": reference_norm,
            "absolute_error_rms": absolute,
            "relative_error": (
                None
                if exact_zero
                else absolute / max(reference_norm, EPSILON_NORM)
            ),
            "relative_error_applicable": not exact_zero,
            "convergence_status": (
                "not_applicable_exact_zero" if exact_zero else "reported_separately"
            ),
        }
    combined_exact_zero = all(exact_zero_components)
    absolute_combined = combined_rms(error)
    reference_combined = combined_rms(reference)
    return {
        "components": components,
        "combined": {
            "value_rms": combined_rms(values),
            "reference_rms": reference_combined,
            "absolute_error_rms": absolute_combined,
            "relative_error": (
                None
                if combined_exact_zero
                else absolute_combined / max(reference_combined, EPSILON_NORM)
            ),
            "relative_error_applicable": not combined_exact_zero,
            "convergence_status": (
                "not_applicable_exact_zero"
                if combined_exact_zero
                else "reported_separately"
            ),
        },
    }


def evaluate_time_slice(
    *,
    resolution: int,
    time: float,
    profile_id: str,
) -> dict[str, Any]:
    arrays = compute_covariant_divergence_slice(
        resolution=resolution,
        time=time,
        profile_id=profile_id,
    )
    residual = _explicit_profile_residual(
        profile_id,
        arrays["fields"],
        f=arrays["f"],
        fp=arrays["fp"],
        time=time,
    )
    assembled = _assembled_profile_residual(
        arrays["fields"], f=arrays["f"], fp=arrays["fp"]
    )
    rhs = residual[None, :, :] * arrays["raised_gradient"]
    metrics = _metric_bundle(arrays["divergence"], rhs)
    return {
        "profile_id": profile_id,
        "resolution_N": resolution,
        "grid_shape": [resolution, resolution],
        "time_t": time,
        "delta_x": 2.0 * math.pi / resolution,
        "delta_y": 2.0 * math.pi / resolution,
        "norm_name": COORDINATE_GRID_NORM_NAME,
        "identity_metrics": metrics,
        "analytic_residual_reference_max_absolute_error": float(
            np.max(np.abs(residual - assembled))
        ),
        "_arrays": {
            **arrays,
            "residual": residual,
            "assembled_residual": assembled,
            "rhs": rhs,
            "identity_error": arrays["divergence"] - rhs,
        },
    }


def _stack_rows(rows: list[dict[str, Any]], name: str) -> np.ndarray:
    return np.stack([row["_arrays"][name] for row in rows], axis=1)


def aggregate_profile_resolution(
    *,
    resolution: int,
    profile_id: str,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    raw_rows = [
        evaluate_time_slice(
            resolution=resolution,
            time=time,
            profile_id=profile_id,
        )
        for time in TIME_SLICES
    ]
    divergence = _stack_rows(raw_rows, "divergence")
    rhs = _stack_rows(raw_rows, "rhs")
    metrics = _metric_bundle(divergence, rhs)
    aggregate = {
        "profile_id": profile_id,
        "resolution_N": resolution,
        "grid_shape": [resolution, resolution],
        "time_slice_count": len(TIME_SLICES),
        "time_slices": list(TIME_SLICES),
        "norm_name": COORDINATE_GRID_NORM_NAME,
        "aggregation": "uniform mean over time,x,y before square root",
        "identity_metrics": metrics,
        "maximum_analytic_residual_reference_absolute_error": max(
            row["analytic_residual_reference_max_absolute_error"]
            for row in raw_rows
        ),
        "_arrays": {
            "divergence": divergence,
            "rhs": rhs,
            "identity_error": divergence - rhs,
            "partial_divergence": _stack_rows(raw_rows, "partial_divergence"),
            "volume_trace_connection_term": _stack_rows(
                raw_rows, "volume_trace_connection_term"
            ),
            "tensor_index_connection_term": _stack_rows(
                raw_rows, "tensor_index_connection_term"
            ),
        },
    }
    public_rows = [
        {key: value for key, value in row.items() if key != "_arrays"}
        for row in raw_rows
    ]
    return aggregate, public_rows


def _cartesian_profile_fields(
    profile_id: str,
    x: np.ndarray,
    y: np.ndarray,
    *,
    time: float,
) -> dict[str, np.ndarray]:
    """Separately coded flat-space profile derivatives for the positive control."""

    zeros = np.zeros_like(x)
    if profile_id == "on_shell_temporal_mode":
        phi = np.full_like(x, AMPLITUDE * math.cos(MASS * time))
        return {
            "phi": phi,
            "t": np.full_like(x, -AMPLITUDE * MASS * math.sin(MASS * time)),
            "x": zeros,
            "y": zeros,
            "tt": -(MASS**2) * phi,
            "tx": zeros,
            "ty": zeros,
            "xx": zeros,
            "yy": zeros,
        }
    if profile_id == "off_shell_x_mode":
        ct = math.cos(X_OMEGA * time)
        st = math.sin(X_OMEGA * time)
        cx = np.cos(X_WAVE_NUMBER * x)
        sx = np.sin(X_WAVE_NUMBER * x)
        phi = AMPLITUDE * ct * cx
        return {
            "phi": phi,
            "t": -AMPLITUDE * X_OMEGA * st * cx,
            "x": -AMPLITUDE * X_WAVE_NUMBER * ct * sx,
            "y": zeros,
            "tt": -(X_OMEGA**2) * phi,
            "tx": AMPLITUDE * X_OMEGA * X_WAVE_NUMBER * st * sx,
            "ty": zeros,
            "xx": -(X_WAVE_NUMBER**2) * phi,
            "yy": zeros,
        }
    if profile_id == "off_shell_y_mode":
        ct = math.cos(Y_OMEGA * time)
        st = math.sin(Y_OMEGA * time)
        cy = np.cos(Y_WAVE_NUMBER * y)
        sy = np.sin(Y_WAVE_NUMBER * y)
        phi = AMPLITUDE * ct * cy
        return {
            "phi": phi,
            "t": -AMPLITUDE * Y_OMEGA * st * cy,
            "x": zeros,
            "y": -AMPLITUDE * Y_WAVE_NUMBER * ct * sy,
            "tt": -(Y_OMEGA**2) * phi,
            "tx": zeros,
            "ty": AMPLITUDE * Y_OMEGA * Y_WAVE_NUMBER * st * sy,
            "xx": zeros,
            "yy": -(Y_WAVE_NUMBER**2) * phi,
        }
    raise ValueError(f"unknown profile_id: {profile_id}")


def _evaluate_cartesian_reference(
    *,
    resolution: int,
    time: float,
    profile_id: str,
) -> dict[str, np.ndarray]:
    spacing = 2.0 * math.pi / resolution
    coordinates = np.arange(resolution, dtype=np.float64) * spacing
    x, y = np.meshgrid(coordinates, coordinates, indexing="ij")
    fields = _cartesian_profile_fields(profile_id, x, y, time=time)
    lower = np.stack([fields["t"], fields["x"], fields["y"]])
    lower_t = np.stack([fields["tt"], fields["tx"], fields["ty"]])
    raised = np.stack([-fields["t"], fields["x"], fields["y"]])
    raised_t = np.stack([-fields["tt"], fields["tx"], fields["ty"]])
    bracket = 0.5 * (
        np.sum(lower * raised, axis=0) + MASS**2 * fields["phi"] ** 2
    )
    bracket_t = np.sum(lower_t * raised, axis=0) + (
        MASS**2 * fields["phi"] * fields["t"]
    )
    stress = np.empty((3, 3, resolution, resolution), dtype=np.float64)
    for mu in range(3):
        for nu in range(3):
            stress[mu, nu] = raised[mu] * raised[nu]
    stress[0, 0] += bracket
    stress[1, 1] -= bracket
    stress[2, 2] -= bracket
    divergence = np.empty((3, resolution, resolution), dtype=np.float64)
    for nu in range(3):
        divergence[nu] = raised_t[0] * raised[nu] + raised[0] * raised_t[nu]
    divergence[0] += bracket_t
    for nu in range(3):
        divergence[nu] += centered_periodic_difference(
            stress[1, nu], spacing, axis=0
        )
        divergence[nu] += centered_periodic_difference(
            stress[2, nu], spacing, axis=1
        )
    residual = (
        -fields["tt"]
        + fields["xx"]
        + fields["yy"]
        - MASS**2 * fields["phi"]
    )
    rhs = residual[None, :, :] * raised
    return {"divergence": divergence, "rhs": rhs}


def flat_limit_verification() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    maximum = 0.0
    for resolution in RESOLUTIONS:
        for profile_id in PROFILE_IDS:
            for time in TIME_SLICES:
                generic = compute_covariant_divergence_slice(
                    resolution=resolution,
                    time=time,
                    profile_id=profile_id,
                    warp_amplitude=0.0,
                )
                generic_fields = generic["fields"]
                flat_residual = (
                    -generic_fields["phi_tt"]
                    + generic_fields["phi_xx"]
                    + generic_fields["phi_yy"]
                    - MASS**2 * generic_fields["phi"]
                )
                generic_rhs = flat_residual[None, :, :] * generic[
                    "raised_gradient"
                ]
                cartesian = _evaluate_cartesian_reference(
                    resolution=resolution,
                    time=time,
                    profile_id=profile_id,
                )
                divergence_error = float(
                    np.max(np.abs(generic["divergence"] - cartesian["divergence"]))
                )
                rhs_error = float(np.max(np.abs(generic_rhs - cartesian["rhs"])))
                row_maximum = max(divergence_error, rhs_error)
                maximum = max(maximum, row_maximum)
                rows.append(
                    {
                        "resolution_N": resolution,
                        "profile_id": profile_id,
                        "time_t": time,
                        "divergence_max_absolute_discrepancy": divergence_error,
                        "rhs_max_absolute_discrepancy": rhs_error,
                        "maximum_absolute_discrepancy": row_maximum,
                    }
                )
    return {
        "method": (
            "generic metric route at epsilon=0 compared with separately coded "
            "Cartesian 2+1 stress-divergence route"
        ),
        "maximum_flat_limit_absolute_discrepancy": maximum,
        "operator_metadata": {
            "coordinate_order": ["t", "x", "y"],
            "operator_coefficients": [-1, 1, 1],
            "connection": 0,
            "curvature": 0,
            "symbolic_metadata_exact": True,
        },
        "rows": rows,
    }


def _control_ratio(defective: np.ndarray, correct: np.ndarray) -> tuple[float, float, float]:
    defective_error = combined_rms(defective)
    correct_error = combined_rms(correct)
    return (
        defective_error,
        correct_error,
        defective_error / max(correct_error, EPSILON_CONTROL),
    )


def _negative_control_records(
    aggregate_by_key: dict[tuple[str, int], dict[str, Any]],
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    records: list[dict[str, Any]] = []
    by_control: dict[str, list[dict[str, Any]]] = {
        "naive_partial_divergence": [],
        "omitted_tensor_index_connection_term": [],
        "omitted_volume_trace_connection_term": [],
        "curved_case_flat_geometry_substitution": [],
        "incorrect_y_inverse_metric_factor": [],
    }
    operations = {
        "naive_partial_divergence": (
            "omit both Gamma^mu_mu_lambda T^lambda_nu and "
            "Gamma^nu_mu_lambda T^mu_lambda"
        ),
        "omitted_tensor_index_connection_term": (
            "omit only Gamma^nu_mu_lambda T^mu_lambda"
        ),
        "omitted_volume_trace_connection_term": (
            "omit only Gamma^mu_mu_lambda T^lambda_nu"
        ),
        "curved_case_flat_geometry_substitution": (
            "set epsilon=0 in metric,inverse metric,connection,stress,and "
            "divergence while retaining the epsilon=0.2 curved RHS"
        ),
        "incorrect_y_inverse_metric_factor": (
            "replace g^yy=f^-2 by g^yy=1 in the defective y residual and "
            "raised y-gradient while retaining the correct curved references"
        ),
    }
    mechanisms = {
        "naive_partial_divergence": "connection terms are required off shell",
        "omitted_tensor_index_connection_term": (
            "the two connection contributions cancel for the temporal mode"
        ),
        "omitted_volume_trace_connection_term": (
            "the two connection contributions cancel for the temporal mode"
        ),
        "curved_case_flat_geometry_substitution": (
            "flat geometry cannot reproduce the curved analytic reference"
        ),
        "incorrect_y_inverse_metric_factor": (
            "the warped y inverse metric is required by both residual and gradient"
        ),
    }

    for resolution in RESOLUTIONS:
        # Multi-profile naive control; each profile remains visible.
        profile_evidence: list[dict[str, Any]] = []
        for profile_id in ("off_shell_x_mode", "off_shell_y_mode"):
            arrays = aggregate_by_key[(profile_id, resolution)]["_arrays"]
            defective = arrays["partial_divergence"] - arrays["rhs"]
            defective_error, correct_error, ratio = _control_ratio(
                defective, arrays["identity_error"]
            )
            profile_evidence.append(
                {
                    "profile_id": profile_id,
                    "defective_error": defective_error,
                    "correct_error": correct_error,
                    "comparison_value": ratio,
                }
            )
        comparison = min(row["comparison_value"] for row in profile_evidence)
        record = {
            "control_id": "naive_partial_divergence",
            "resolution_N": resolution,
            "exact_defective_operation": operations["naive_partial_divergence"],
            "expected_mechanism": mechanisms["naive_partial_divergence"],
            "profile_evidence": profile_evidence,
            "adjudication": "minimum profile-specific error ratio",
            "comparison_value": comparison,
            "threshold": MINIMUM_CONNECTION_CONTROL_RATIO,
            "comparison": ">=",
            "pass": comparison >= MINIMUM_CONNECTION_CONTROL_RATIO,
        }
        records.append(record)
        by_control[record["control_id"]].append(record)

        temporal = aggregate_by_key[("on_shell_temporal_mode", resolution)][
            "_arrays"
        ]
        connection_defects = {
            "omitted_tensor_index_connection_term": (
                temporal["partial_divergence"]
                + temporal["volume_trace_connection_term"]
                - temporal["rhs"]
            ),
            "omitted_volume_trace_connection_term": (
                temporal["partial_divergence"]
                + temporal["tensor_index_connection_term"]
                - temporal["rhs"]
            ),
        }
        for control_id, defective in connection_defects.items():
            defective_error, correct_error, ratio = _control_ratio(
                defective, temporal["identity_error"]
            )
            record = {
                "control_id": control_id,
                "resolution_N": resolution,
                "exact_defective_operation": operations[control_id],
                "expected_mechanism": mechanisms[control_id],
                "profile_evidence": [
                    {
                        "profile_id": "on_shell_temporal_mode",
                        "defective_error": defective_error,
                        "correct_error": correct_error,
                        "comparison_value": ratio,
                    }
                ],
                "adjudication": "temporal profile error ratio",
                "comparison_value": ratio,
                "threshold": MINIMUM_CONNECTION_CONTROL_RATIO,
                "comparison": ">=",
                "pass": ratio >= MINIMUM_CONNECTION_CONTROL_RATIO,
            }
            records.append(record)
            by_control[control_id].append(record)

        flat_profile_evidence: list[dict[str, Any]] = []
        for profile_id in ("off_shell_x_mode", "off_shell_y_mode"):
            curved = aggregate_by_key[(profile_id, resolution)]["_arrays"]
            flat_divergences = []
            for time in TIME_SLICES:
                flat_divergences.append(
                    compute_covariant_divergence_slice(
                        resolution=resolution,
                        time=time,
                        profile_id=profile_id,
                        warp_amplitude=0.0,
                    )["divergence"]
                )
            flat_divergence = np.stack(flat_divergences, axis=1)
            defective_error = combined_rms(flat_divergence - curved["rhs"])
            normalization = combined_rms(curved["rhs"])
            discrepancy = defective_error / max(normalization, EPSILON_CONTROL)
            flat_profile_evidence.append(
                {
                    "profile_id": profile_id,
                    "defective_error": defective_error,
                    "normalization_norm": normalization,
                    "comparison_value": discrepancy,
                }
            )
        comparison = min(
            row["comparison_value"] for row in flat_profile_evidence
        )
        record = {
            "control_id": "curved_case_flat_geometry_substitution",
            "resolution_N": resolution,
            "exact_defective_operation": operations[
                "curved_case_flat_geometry_substitution"
            ],
            "expected_mechanism": mechanisms[
                "curved_case_flat_geometry_substitution"
            ],
            "profile_evidence": flat_profile_evidence,
            "adjudication": "minimum profile-specific normalized discrepancy",
            "comparison_value": comparison,
            "threshold": MINIMUM_GEOMETRY_DEFECT_DISCREPANCY,
            "comparison": ">=",
            "pass": comparison >= MINIMUM_GEOMETRY_DEFECT_DISCREPANCY,
        }
        records.append(record)
        by_control[record["control_id"]].append(record)

        y_arrays = aggregate_by_key[("off_shell_y_mode", resolution)]["_arrays"]
        wrong_rhs_rows: list[np.ndarray] = []
        for time in TIME_SLICES:
            slice_arrays = compute_covariant_divergence_slice(
                resolution=resolution,
                time=time,
                profile_id="off_shell_y_mode",
            )
            wrong_residual = _explicit_profile_residual(
                "off_shell_y_mode",
                slice_arrays["fields"],
                f=slice_arrays["f"],
                fp=slice_arrays["fp"],
                time=time,
                wrong_y_inverse_metric=True,
            )
            wrong_raised = np.array(slice_arrays["raised_gradient"], copy=True)
            wrong_raised[2] = slice_arrays["fields"]["phi_y"]
            wrong_rhs_rows.append(wrong_residual[None, :, :] * wrong_raised)
        wrong_rhs = np.stack(wrong_rhs_rows, axis=1)
        defective_error = combined_rms(wrong_rhs - y_arrays["rhs"])
        defective_identity_error_against_correct_divergence = combined_rms(
            y_arrays["divergence"] - wrong_rhs
        )
        correct_error = combined_rms(y_arrays["identity_error"])
        normalization = combined_rms(y_arrays["rhs"])
        discrepancy = defective_error / max(normalization, EPSILON_CONTROL)
        record = {
            "control_id": "incorrect_y_inverse_metric_factor",
            "resolution_N": resolution,
            "exact_defective_operation": operations[
                "incorrect_y_inverse_metric_factor"
            ],
            "expected_mechanism": mechanisms[
                "incorrect_y_inverse_metric_factor"
            ],
            "profile_evidence": [
                {
                    "profile_id": "off_shell_y_mode",
                    "defective_error": defective_error,
                    "defective_identity_error_against_correct_divergence": (
                        defective_identity_error_against_correct_divergence
                    ),
                    "correct_error": correct_error,
                    "normalization_norm": normalization,
                    "comparison_value": discrepancy,
                }
            ],
            "adjudication": "y-profile normalized discrepancy",
            "comparison_value": discrepancy,
            "threshold": MINIMUM_GEOMETRY_DEFECT_DISCREPANCY,
            "comparison": ">=",
            "pass": discrepancy >= MINIMUM_GEOMETRY_DEFECT_DISCREPANCY,
        }
        records.append(record)
        by_control[record["control_id"]].append(record)

    adjudication: dict[str, Any] = {}
    for control_id, control_rows in by_control.items():
        finest = next(
            row for row in control_rows if row["resolution_N"] == RESOLUTIONS[-1]
        )
        adjudication[control_id] = {
            "resolution_N": RESOLUTIONS[-1],
            "comparison_value": finest["comparison_value"],
            "threshold": finest["threshold"],
            "pass": finest["pass"],
        }
    adjudication["all_five_negative_controls_passed"] = all(
        value["pass"]
        for key, value in adjudication.items()
        if key != "all_five_negative_controls_passed"
    )
    return records, adjudication


def _orders(values: list[float]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for index in range(len(values) - 1):
        coarse = values[index]
        fine = values[index + 1]
        if coarse <= 0.0 or fine <= 0.0:
            order: float | None = None
            status = "not_computable_nonpositive_error"
        else:
            order = math.log2(coarse / fine)
            status = "reported"
        rows.append(
            {
                "coarse_N": RESOLUTIONS[index],
                "fine_N": RESOLUTIONS[index + 1],
                "order": order,
                "status": status,
            }
        )
    return rows


def _convergence_diagnostics(
    aggregate_by_key: dict[tuple[str, int], dict[str, Any]],
) -> dict[str, Any]:
    diagnostics: dict[str, Any] = {}
    metric_keys = (*COMPONENT_LABELS, "combined")
    for profile_id in PROFILE_IDS:
        profile: dict[str, Any] = {}
        for metric_key in metric_keys:
            first_metrics = aggregate_by_key[(profile_id, RESOLUTIONS[0])][
                "identity_metrics"
            ]
            if metric_key == "combined":
                first_metric = first_metrics["combined"]
                errors = [
                    aggregate_by_key[(profile_id, resolution)][
                        "identity_metrics"
                    ]["combined"]["absolute_error_rms"]
                    for resolution in RESOLUTIONS
                ]
            else:
                first_metric = first_metrics["components"][metric_key]
                errors = [
                    aggregate_by_key[(profile_id, resolution)][
                        "identity_metrics"
                    ]["components"][metric_key]["absolute_error_rms"]
                    for resolution in RESOLUTIONS
                ]
            if not first_metric["relative_error_applicable"]:
                profile[metric_key] = {
                    "errors": errors,
                    "orders": [],
                    "convergence_status": "not_applicable_exact_zero",
                    "minimum_two_finest_order": None,
                    "p_64_128": None,
                    "p_128_256": None,
                    "p_min": None,
                }
                continue
            orders = _orders(errors)
            p_64_128 = orders[1]["order"]
            p_128_256 = orders[2]["order"]
            finest_orders = [p_64_128, p_128_256]
            profile[metric_key] = {
                "errors": errors,
                "orders": orders,
                "convergence_status": "reported",
                "minimum_two_finest_order": min(finest_orders),
                "p_64_128": p_64_128,
                "p_128_256": p_128_256,
                "p_min": min(finest_orders),
            }
        diagnostics[profile_id] = profile
    return diagnostics


def _expected_success_criteria() -> dict[str, float | bool]:
    return {
        "all_thresholds_required": True,
        "maximum_curvature_route_absolute_discrepancy": (
            MAXIMUM_CURVATURE_ROUTE_ERROR
        ),
        "maximum_analytic_profile_residual_reference_error": (
            MAXIMUM_ANALYTIC_REFERENCE_ERROR
        ),
        "maximum_finest_on_shell_combined_absolute_divergence_error": (
            MAXIMUM_ON_SHELL_DIVERGENCE
        ),
        "maximum_finest_x_mode_combined_relative_identity_error": (
            MAXIMUM_FINEST_RELATIVE_ERROR
        ),
        "maximum_finest_y_mode_combined_relative_identity_error": (
            MAXIMUM_FINEST_RELATIVE_ERROR
        ),
        "maximum_flat_limit_absolute_discrepancy": MAXIMUM_FLAT_LIMIT_ERROR,
        "maximum_metric_compatibility_absolute_error": (
            MAXIMUM_METRIC_COMPATIBILITY_ERROR
        ),
        "minimum_curvature_peak_absolute_value": (
            MINIMUM_PEAK_ABSOLUTE_CURVATURE
        ),
        "minimum_curvature_peak_to_peak_variation": MINIMUM_CURVATURE_VARIATION,
        "minimum_flat_geometry_substitution_normalized_discrepancy": (
            MINIMUM_GEOMETRY_DEFECT_DISCREPANCY
        ),
        "minimum_incorrect_y_inverse_metric_normalized_discrepancy": (
            MINIMUM_GEOMETRY_DEFECT_DISCREPANCY
        ),
        "minimum_naive_partial_divergence_error_ratio": (
            MINIMUM_CONNECTION_CONTROL_RATIO
        ),
        "minimum_omitted_tensor_index_term_error_ratio": (
            MINIMUM_CONNECTION_CONTROL_RATIO
        ),
        "minimum_omitted_volume_trace_term_error_ratio": (
            MINIMUM_CONNECTION_CONTROL_RATIO
        ),
        "minimum_two_finest_x_mode_convergence_order": (
            MINIMUM_CONVERGENCE_ORDER
        ),
        "minimum_two_finest_y_mode_convergence_order": (
            MINIMUM_CONVERGENCE_ORDER
        ),
    }


def _validated_thresholds(guardrail: dict[str, Any]) -> dict[str, float | bool]:
    criteria = guardrail.get("success_criteria")
    expected = _expected_success_criteria()
    if criteria != expected:
        raise ValueError(
            "v1 guardrail success_criteria do not match the calculation's "
            "frozen sixteen-decision contract"
        )
    if guardrail.get("revised_at_utc") != GUARDRAIL_REVISED_AT_UTC:
        raise ValueError("v1 guardrail revised_at_utc is not the frozen value")
    zero_policy = guardrail["curvature_verification"][
        "curvature_zero_exclusion_policy"
    ]
    norm_contract = guardrail["numerical_method"]["norm_contract"]
    if zero_policy["epsilon_R"] != EPSILON_R:
        raise ValueError("v1 guardrail epsilon_R does not match calculation")
    if (
        norm_contract["epsilon_norm"] != EPSILON_NORM
        or norm_contract["epsilon_control"] != EPSILON_CONTROL
        or norm_contract["name"]
        != COORDINATE_GRID_NORM_NAME
    ):
        raise ValueError("v1 guardrail norm contract does not match calculation")
    decision_ids = [
        row["threshold_id"] for row in guardrail["threshold_decisions"]
    ]
    if len(decision_ids) != 16 or set(decision_ids) != (
        set(expected) - {"all_thresholds_required"}
    ):
        raise ValueError("v1 guardrail threshold_decisions are not the exact 16")
    return criteria


def _public_aggregate(aggregate: dict[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in aggregate.items() if key != "_arrays"}


def build_result(*, captured_at_utc: str = CAPTURED_AT_UTC) -> dict[str, Any]:
    guardrail, guardrail_sha256 = load_guardrail()
    thresholds = _validated_thresholds(guardrail)
    raw_aggregates: list[dict[str, Any]] = []
    public_rows: list[dict[str, Any]] = []
    aggregate_by_key: dict[tuple[str, int], dict[str, Any]] = {}
    for profile_id in PROFILE_IDS:
        for resolution in RESOLUTIONS:
            aggregate, rows = aggregate_profile_resolution(
                resolution=resolution,
                profile_id=profile_id,
            )
            raw_aggregates.append(aggregate)
            public_rows.extend(rows)
            aggregate_by_key[(profile_id, resolution)] = aggregate

    convergence = _convergence_diagnostics(aggregate_by_key)
    geometry_safety = geometry_safety_verification()
    curvature = curvature_verification()
    flat_limit = flat_limit_verification()
    control_records, control_adjudication = _negative_control_records(
        aggregate_by_key
    )

    finest_x = aggregate_by_key[("off_shell_x_mode", RESOLUTIONS[-1])]
    finest_y = aggregate_by_key[("off_shell_y_mode", RESOLUTIONS[-1])]
    finest_temporal = aggregate_by_key[
        ("on_shell_temporal_mode", RESOLUTIONS[-1])
    ]
    maximum_reference_error = max(
        row["maximum_analytic_residual_reference_absolute_error"]
        for row in raw_aggregates
    )
    x_order = convergence["off_shell_x_mode"]["combined"][
        "minimum_two_finest_order"
    ]
    y_order = convergence["off_shell_y_mode"]["combined"][
        "minimum_two_finest_order"
    ]
    x_relative = finest_x["identity_metrics"]["combined"]["relative_error"]
    y_relative = finest_y["identity_metrics"]["combined"]["relative_error"]
    on_shell_error = finest_temporal["identity_metrics"]["combined"][
        "absolute_error_rms"
    ]
    control = control_adjudication
    evidence = {
        "minimum_two_finest_x_mode_convergence_order": x_order,
        "minimum_two_finest_y_mode_convergence_order": y_order,
        "finest_x_mode_combined_relative_identity_error": x_relative,
        "finest_y_mode_combined_relative_identity_error": y_relative,
        "finest_on_shell_combined_absolute_divergence_error": on_shell_error,
        "maximum_analytic_profile_residual_reference_error": (
            maximum_reference_error
        ),
        "maximum_metric_compatibility_absolute_error": curvature[
            "maximum_metric_compatibility_absolute_error"
        ],
        "maximum_curvature_route_absolute_discrepancy": curvature[
            "maximum_curvature_route_absolute_discrepancy"
        ],
        "peak_absolute_scalar_curvature": curvature[
            "peak_absolute_scalar_curvature"
        ],
        "curvature_peak_to_peak_variation": curvature[
            "peak_to_peak_scalar_curvature"
        ],
        "maximum_flat_limit_absolute_discrepancy": flat_limit[
            "maximum_flat_limit_absolute_discrepancy"
        ],
        "naive_partial_divergence_minimum_profile_ratio": control[
            "naive_partial_divergence"
        ]["comparison_value"],
        "omitted_tensor_index_term_error_ratio": control[
            "omitted_tensor_index_connection_term"
        ]["comparison_value"],
        "omitted_volume_trace_term_error_ratio": control[
            "omitted_volume_trace_connection_term"
        ]["comparison_value"],
        "flat_geometry_substitution_minimum_profile_normalized_discrepancy": (
            control["curved_case_flat_geometry_substitution"]["comparison_value"]
        ),
        "incorrect_y_inverse_metric_normalized_discrepancy": control[
            "incorrect_y_inverse_metric_factor"
        ]["comparison_value"],
    }
    checks = {
        "minimum_two_finest_x_mode_convergence_order": (
            x_order >= thresholds["minimum_two_finest_x_mode_convergence_order"]
        ),
        "minimum_two_finest_y_mode_convergence_order": (
            y_order >= thresholds["minimum_two_finest_y_mode_convergence_order"]
        ),
        "maximum_finest_x_mode_combined_relative_identity_error": (
            x_relative
            <= thresholds[
                "maximum_finest_x_mode_combined_relative_identity_error"
            ]
        ),
        "maximum_finest_y_mode_combined_relative_identity_error": (
            y_relative
            <= thresholds[
                "maximum_finest_y_mode_combined_relative_identity_error"
            ]
        ),
        "maximum_finest_on_shell_combined_absolute_divergence_error": (
            on_shell_error
            <= thresholds[
                "maximum_finest_on_shell_combined_absolute_divergence_error"
            ]
        ),
        "maximum_analytic_profile_residual_reference_error": (
            maximum_reference_error
            <= thresholds[
                "maximum_analytic_profile_residual_reference_error"
            ]
        ),
        "maximum_metric_compatibility_absolute_error": (
            evidence["maximum_metric_compatibility_absolute_error"]
            <= thresholds["maximum_metric_compatibility_absolute_error"]
        ),
        "maximum_curvature_route_absolute_discrepancy": (
            evidence["maximum_curvature_route_absolute_discrepancy"]
            <= thresholds["maximum_curvature_route_absolute_discrepancy"]
        ),
        "minimum_curvature_peak_absolute_value": (
            evidence["peak_absolute_scalar_curvature"]
            >= thresholds["minimum_curvature_peak_absolute_value"]
        ),
        "minimum_curvature_peak_to_peak_variation": (
            evidence["curvature_peak_to_peak_variation"]
            >= thresholds["minimum_curvature_peak_to_peak_variation"]
        ),
        "maximum_flat_limit_absolute_discrepancy": (
            evidence["maximum_flat_limit_absolute_discrepancy"]
            <= thresholds["maximum_flat_limit_absolute_discrepancy"]
        ),
        "minimum_naive_partial_divergence_error_ratio": control[
            "naive_partial_divergence"
        ]["pass"],
        "minimum_omitted_tensor_index_term_error_ratio": control[
            "omitted_tensor_index_connection_term"
        ]["pass"],
        "minimum_omitted_volume_trace_term_error_ratio": control[
            "omitted_volume_trace_connection_term"
        ]["pass"],
        "minimum_flat_geometry_substitution_normalized_discrepancy": control[
            "curved_case_flat_geometry_substitution"
        ]["pass"],
        "minimum_incorrect_y_inverse_metric_normalized_discrepancy": control[
            "incorrect_y_inverse_metric_factor"
        ]["pass"],
    }
    passed = len(checks) == 16 and all(checks.values())
    next_target = RESULT_REVIEW_TARGET if passed else THRESHOLD_FAILURE_TARGET
    ordered_decisions = []
    for frozen in guardrail["threshold_decisions"]:
        threshold_id = frozen["threshold_id"]
        ordered_decisions.append(
            {
                **frozen,
                "observed_value": evidence[
                    {
                        "minimum_two_finest_x_mode_convergence_order": (
                            "minimum_two_finest_x_mode_convergence_order"
                        ),
                        "minimum_two_finest_y_mode_convergence_order": (
                            "minimum_two_finest_y_mode_convergence_order"
                        ),
                        "maximum_finest_x_mode_combined_relative_identity_error": (
                            "finest_x_mode_combined_relative_identity_error"
                        ),
                        "maximum_finest_y_mode_combined_relative_identity_error": (
                            "finest_y_mode_combined_relative_identity_error"
                        ),
                        "maximum_finest_on_shell_combined_absolute_divergence_error": (
                            "finest_on_shell_combined_absolute_divergence_error"
                        ),
                        "maximum_analytic_profile_residual_reference_error": (
                            "maximum_analytic_profile_residual_reference_error"
                        ),
                        "maximum_metric_compatibility_absolute_error": (
                            "maximum_metric_compatibility_absolute_error"
                        ),
                        "maximum_curvature_route_absolute_discrepancy": (
                            "maximum_curvature_route_absolute_discrepancy"
                        ),
                        "minimum_curvature_peak_absolute_value": (
                            "peak_absolute_scalar_curvature"
                        ),
                        "minimum_curvature_peak_to_peak_variation": (
                            "curvature_peak_to_peak_variation"
                        ),
                        "maximum_flat_limit_absolute_discrepancy": (
                            "maximum_flat_limit_absolute_discrepancy"
                        ),
                        "minimum_naive_partial_divergence_error_ratio": (
                            "naive_partial_divergence_minimum_profile_ratio"
                        ),
                        "minimum_omitted_tensor_index_term_error_ratio": (
                            "omitted_tensor_index_term_error_ratio"
                        ),
                        "minimum_omitted_volume_trace_term_error_ratio": (
                            "omitted_volume_trace_term_error_ratio"
                        ),
                        "minimum_flat_geometry_substitution_normalized_discrepancy": (
                            "flat_geometry_substitution_minimum_profile_normalized_discrepancy"
                        ),
                        "minimum_incorrect_y_inverse_metric_normalized_discrepancy": (
                            "incorrect_y_inverse_metric_normalized_discrepancy"
                        ),
                    }[threshold_id]
                ],
                "pass": checks[threshold_id],
            }
        )

    return {
        "schema_id": f"{CALCULATION_ID}-RESULT",
        "calculation_id": CALCULATION_ID,
        "calculation_status": (
            "executed_pending_result_review" if passed else "executed_blocked"
        ),
        "captured_at_utc": captured_at_utc,
        "guardrail": {
            "path": GUARDRAIL_RELATIVE_PATH,
            "sha256": guardrail_sha256,
            "schema_id": guardrail["schema_id"],
            "revised_at_utc": guardrail.get(
                "revised_at_utc", GUARDRAIL_REVISED_AT_UTC
            ),
        },
        "question": (
            "Does the scalar covariant stress-energy divergence identity hold "
            "for three profiles and all three components on one fixed 2+1 "
            "warped periodic background?"
        ),
        "background_geometry_classification": BACKGROUND_GEOMETRY_CLASSIFICATION,
        "spacetime_dimension": 3,
        "background_geometry": {
            "metric": "g_mu_nu = diag(-1,1,f(x)^2)",
            "inverse_metric": "g^mu_nu = diag(-1,1,f(x)^(-2))",
            "warp_factor": "f(x)=1+0.2*cos(x)",
            "determinant": "det(g)=-f(x)^2",
            "minimum_warp_factor": 0.8,
            "maximum_warp_factor": 1.2,
            "maximum_inverse_y_metric_factor": 1.5625,
            "minimum_absolute_determinant": 0.64,
            "scalar_curvature_minimum": -0.5,
            "scalar_curvature_maximum": 1.0 / 3.0,
            "curvature_zero_crossings": [math.pi / 2.0, 3.0 * math.pi / 2.0],
            "nonzero_christoffel_symbols": {
                "Gamma^x_yy": "-f*f'",
                "Gamma^y_xy": "f'/f",
                "Gamma^y_yx": "f'/f",
            },
        },
        "mathematical_convention": {
            "potential": "V(phi)=1/2*m^2*phi^2",
            "potential_derivative": "V'(phi)=m^2*phi",
            "field_residual": "E_phi=Box_g(phi)-m^2*phi",
            "identity": "nabla_mu T^{mu nu}=E_phi*nabla^nu phi",
            "volume_trace_connection_term": (
                "Gamma^mu_mu_lambda*T^{lambda nu}"
            ),
            "tensor_index_connection_term": (
                "Gamma^nu_mu_lambda*T^{mu lambda}"
            ),
        },
        "analytic_profile_references": {
            "on_shell_temporal_mode": "E_phi=0",
            "off_shell_x_mode": (
                "E_phi=(omega_x^2-m^2-k^2)*phi_x-"
                "A*k*(f'/f)*cos(omega_x*t)*sin(k*x)"
            ),
            "off_shell_y_mode": (
                "E_phi=(omega_y^2-m^2-ell^2/f^2)*phi_y="
                "(1.25-4/f^2)*phi_y"
            ),
        },
        "parameters": {
            "amplitude_A": AMPLITUDE,
            "mass_m": MASS,
            "warp_amplitude_epsilon": WARP_AMPLITUDE,
            "x_wave_number_k": X_WAVE_NUMBER,
            "y_wave_number_ell": Y_WAVE_NUMBER,
            "omega_x": X_OMEGA,
            "omega_y": Y_OMEGA,
            "time_slices": list(TIME_SLICES),
            "resolutions_N": list(RESOLUTIONS),
            "grid_interpretation": "N means N x N",
            "epsilon_R": EPSILON_R,
            "epsilon_norm": EPSILON_NORM,
            "epsilon_control": EPSILON_CONTROL,
        },
        "method": {
            "meshgrid_indexing": "ij",
            "periodic_endpoints_duplicated": False,
            "temporal_field_derivatives": "analytic product rule",
            "spatial_divergence_derivatives": (
                "second-order centered periodic differences"
            ),
            "curvature_route": "generic tensor index loops with analytic dg,ddg",
            "norm_name": COORDINATE_GRID_NORM_NAME,
            "norm_is_coordinate_invariant": False,
            "norm_is_volume_weighted": False,
            "raw_grids_persisted": False,
        },
        "geometry_safety_verification": geometry_safety,
        "geometry_verification": curvature,
        "profile_time_resolution_row_count": len(public_rows),
        "profile_time_resolution_rows": public_rows,
        "profile_resolution_aggregate_count": len(raw_aggregates),
        "profile_resolution_aggregates": [
            _public_aggregate(row) for row in raw_aggregates
        ],
        "convergence_diagnostics": convergence,
        "flat_limit_control": flat_limit,
        "negative_controls": {
            "record_count": len(control_records),
            "records": control_records,
            "finest_resolution_adjudication": control_adjudication,
        },
        "thresholds": thresholds,
        "threshold_evidence": evidence,
        "threshold_checks": checks,
        "threshold_decisions": ordered_decisions,
        "frozen_threshold_count": len(checks),
        "all_thresholds_passed": passed,
        "selected_next_target": next_target,
        "claim": {
            "primary_label": "E-REPRO" if passed else "B-BLOCKED",
            "claim_status": (
                "generated_pending_result_review"
                if passed
                else "blocked_threshold_failure"
            ),
            "claim_ceiling_level": 3,
            "claim_scope": (
                "one fixed-background fixed-coordinate 2+1 scalar matter "
                "identity calculation only"
            ),
            "next_work_status": next_target,
        },
        "existing_equation_id_reused": EQUATION_ID,
        "equation_compendium_edited": False,
        "boundary": {
            "calculation_executed": True,
            "spacetime_dimension": 3,
            "two_dimensional_Einstein_degeneracy_not_applicable": True,
            "einstein_tensor_can_be_nonzero": True,
            "background_fixed": True,
            "gravity_evolved": False,
            "background_metric_evolved": False,
            "einstein_equation_solved": False,
            "Einstein_source_tested": False,
            "source_admissibility_claimed": False,
            "bianchi_compatibility_claimed": False,
            "qft_gr_seam_admissibility_claimed": False,
            "qft_gr_seam_closure_claimed": False,
            "quantum_or_renormalized_stress_energy_claimed": False,
            "multi_background_robustness_claimed": False,
            "level_4_or_level_5_claimed": False,
            "ccft_resumed": False,
            "master_action_promoted": False,
        },
        "result_review": {
            "status": (
                "pending" if passed else "not_created_threshold_failure"
            ),
            "target": RESULT_REVIEW_TARGET if passed else None,
        },
    }


def _blas_lapack_metadata() -> dict[str, Any]:
    config = getattr(np.__config__, "CONFIG", {})
    dependencies = config.get("Build Dependencies", {})
    result: dict[str, Any] = {}
    for name in ("blas", "lapack"):
        dependency = dependencies.get(name, {})
        result[name] = {
            "name": dependency.get("name", "unknown"),
            "version": dependency.get("version", "unknown"),
        }
    return result


def stable_environment_metadata() -> dict[str, Any]:
    return {
        "python_version": platform.python_version(),
        "numpy_version": np.__version__,
        "operating_system_family": platform.system(),
        "machine_architecture": platform.machine(),
        "endianness": sys.byteorder,
        "blas_lapack": _blas_lapack_metadata(),
    }


def build_manifest(
    *,
    output_path: Path,
    result: dict[str, Any] | None = None,
    captured_at_utc: str = CAPTURED_AT_UTC,
) -> dict[str, Any]:
    guardrail, guardrail_sha256 = load_guardrail()
    if result is None:
        result = json.loads(output_path.read_text(encoding="utf-8"))
    return {
        "schema_id": f"{CALCULATION_ID}-MANIFEST",
        "calculation_id": CALCULATION_ID,
        "captured_at_utc": captured_at_utc,
        "guardrail_path": GUARDRAIL_RELATIVE_PATH,
        "guardrail_schema_id": guardrail["schema_id"],
        "guardrail_sha256": guardrail_sha256,
        "script_path": SCRIPT_RELATIVE_PATH,
        "script_sha256": sha256_file(REPO_ROOT / SCRIPT_RELATIVE_PATH),
        "test_path": TEST_RELATIVE_PATH,
        "execution_command": EXECUTION_COMMAND,
        "environment": stable_environment_metadata(),
        "output_path": OUTPUT_RELATIVE_PATH,
        "output_sha256": sha256_file(output_path),
        "execution_report_path": EXECUTION_REPORT_RELATIVE_PATH,
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
        "temporary_output_paths_serialized": False,
        "wall_clock_timestamp_serialized": False,
        "background_geometry_classification": (
            BACKGROUND_GEOMETRY_CLASSIFICATION
        ),
        "spacetime_dimension": 3,
        "claim_label": result["claim"]["primary_label"],
        "claim_scope": result["claim"]["claim_scope"],
        "claim_ceiling_level": 3,
        "all_thresholds_passed": result["all_thresholds_passed"],
        "result_review_status": result["result_review"]["status"],
        "result_review_target": result["result_review"]["target"],
        "selected_next_target": result["selected_next_target"],
        "boundary": result["boundary"],
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
        result=result,
        captured_at_utc=captured_at_utc,
    )
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_path.write_bytes(canonical_json_bytes(manifest))
    return result, manifest


def _resolve(path: Path) -> Path:
    return path if path.is_absolute() else REPO_ROOT / path


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Execute the fixed 2+1 warped-background scalar covariant "
            "stress-energy divergence identity calculation."
        )
    )
    parser.add_argument("--output", type=Path, default=Path(OUTPUT_RELATIVE_PATH))
    parser.add_argument(
        "--manifest", type=Path, default=Path(MANIFEST_RELATIVE_PATH)
    )
    args = parser.parse_args(argv)
    output_path = _resolve(args.output)
    manifest_path = _resolve(args.manifest)
    result, manifest = write_artifacts(
        output_path=output_path,
        manifest_path=manifest_path,
    )
    print(
        json.dumps(
            {
                "calculation_id": CALCULATION_ID,
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
