from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Any, Iterable

import numpy as np
from numpy.polynomial.legendre import leggauss


G_SI = 6.67430e-11
A_Y = 1.0 / 3.0
DENSITY = 19250.0
RADIUS_D = 5e-3
RADIUS_A = 5e-3
LEVER_D = 3e-2
LEVER_A = 3e-2
LAMBDA_REFERENCE = 1e-3
GAPS = np.logspace(-4.0, -2.0, 25, dtype=np.float64)
LAMBDA_GRID = np.logspace(-5.0, -1.0, 25, dtype=np.float64)
HARMONICS = (2, 4, 6)
PARAMETER_ORDER = (
    "LOG_LAMBDA",
    "TORQUE_CALIBRATION",
    "SOURCE_DENSITY_SCALE",
    "DETECTOR_DENSITY_SCALE",
    "DETECTOR_LEVER_OFFSET",
    "ATTRACTOR_LEVER_OFFSET",
    "GAP_OFFSET",
    "ATTRACTOR_AXIS_X_OFFSET",
    "ATTRACTOR_AXIS_Y_OFFSET",
    "ANGULAR_ZERO_OFFSET",
    "HARMONIC_LEAKAGE",
    "BACKGROUND_2RE",
    "BACKGROUND_2IM",
    "BACKGROUND_4RE",
    "BACKGROUND_4IM",
    "BACKGROUND_6RE",
    "BACKGROUND_6IM",
)
FINITE_DIFFERENCE_COLUMNS = (
    "LOG_LAMBDA",
    "DETECTOR_LEVER_OFFSET",
    "ATTRACTOR_LEVER_OFFSET",
    "GAP_OFFSET",
    "ATTRACTOR_AXIS_X_OFFSET",
    "ATTRACTOR_AXIS_Y_OFFSET",
    "ANGULAR_ZERO_OFFSET",
)
EXACT_LINEAR_COLUMNS = tuple(
    item for item in PARAMETER_ORDER if item not in FINITE_DIFFERENCE_COLUMNS
)
SCALES = {
    "TORQUE_CALIBRATION": 0.02,
    "SOURCE_DENSITY_SCALE": 0.01,
    "DETECTOR_DENSITY_SCALE": 0.01,
    "DETECTOR_LEVER_OFFSET": 1e-4,
    "ATTRACTOR_LEVER_OFFSET": 1e-4,
    "GAP_OFFSET": 1e-5,
    "ATTRACTOR_AXIS_X_OFFSET": 1e-4,
    "ATTRACTOR_AXIS_Y_OFFSET": 1e-4,
    "ANGULAR_ZERO_OFFSET": 1e-3,
    "HARMONIC_LEAKAGE": 0.002,
    "BACKGROUND_2RE": 1e-17,
    "BACKGROUND_2IM": 1e-17,
    "BACKGROUND_4RE": 1e-17,
    "BACKGROUND_4IM": 1e-17,
    "BACKGROUND_6RE": 1e-17,
    "BACKGROUND_6IM": 1e-17,
}
BACKGROUND_INDEX = {
    "BACKGROUND_2RE": 0,
    "BACKGROUND_2IM": 1,
    "BACKGROUND_4RE": 2,
    "BACKGROUND_4IM": 3,
    "BACKGROUND_6RE": 4,
    "BACKGROUND_6IM": 5,
}


@dataclass(frozen=True)
class ApparatusParameters:
    torque_calibration: float = 0.0
    source_density_scale: float = 0.0
    detector_density_scale: float = 0.0
    detector_lever_offset_m: float = 0.0
    attractor_lever_offset_m: float = 0.0
    gap_offset_m: float = 0.0
    attractor_axis_x_offset_m: float = 0.0
    attractor_axis_y_offset_m: float = 0.0
    angular_zero_offset_rad: float = 0.0
    harmonic_leakage: float = 0.0
    backgrounds_nm: tuple[float, float, float, float, float, float] = (
        0.0,
        0.0,
        0.0,
        0.0,
        0.0,
        0.0,
    )


def sphere_mass(radius_m: float, density_kg_m3: float) -> float:
    return (4.0 / 3.0) * math.pi * radius_m**3 * density_kg_m3


def uniform_sphere_form_factor(x: float | np.ndarray) -> float | np.ndarray:
    values = np.asarray(x, dtype=np.float64)
    small = np.abs(values) < 1e-3
    out = np.empty_like(values)
    if np.any(small):
        xs = values[small]
        x2 = xs * xs
        out[small] = 1.0 + x2 / 10.0 + x2 * x2 / 280.0 + x2**3 / 15120.0
    if np.any(~small):
        xl = values[~small]
        out[~small] = 3.0 * (xl * np.cosh(xl) - np.sinh(xl)) / xl**3
    if out.ndim == 0:
        return float(out)
    return out


def scaled_uniform_sphere_form_factor(x: float | np.ndarray) -> float | np.ndarray:
    values = np.asarray(x, dtype=np.float64)
    small = np.abs(values) < 1e-3
    out = np.empty_like(values)
    if np.any(small):
        out[small] = np.exp(-values[small]) * np.asarray(
            uniform_sphere_form_factor(values[small])
        )
    if np.any(~small):
        xl = values[~small]
        out[~small] = (
            3.0
            * ((xl - 1.0) + (xl + 1.0) * np.exp(-2.0 * xl))
            / (2.0 * xl**3)
        )
    if out.ndim == 0:
        return float(out)
    return out


def pair_energy_and_radial_derivative(
    distance_m: np.ndarray | float,
    lambda_m: float,
    *,
    mass_d_kg: float,
    mass_a_kg: float,
    radius_d_m: float = RADIUS_D,
    radius_a_m: float = RADIUS_A,
    yukawa_amplitude: float = A_Y,
    component: str = "total",
    yukawa_sign: float = 1.0,
    remove_attractor_form_factor: bool = False,
) -> tuple[np.ndarray, np.ndarray]:
    r = np.asarray(distance_m, dtype=np.float64)
    if np.any(r <= 0.0):
        raise ValueError("pair distance must be positive")
    prefactor = G_SI * mass_d_kg * mass_a_kg
    newton_energy = -prefactor / r
    newton_derivative = prefactor / r**2
    yukawa_energy = np.zeros_like(r)
    yukawa_derivative = np.zeros_like(r)
    if lambda_m > 0.0:
        xd = radius_d_m / lambda_m
        xa = radius_a_m / lambda_m
        hd = float(scaled_uniform_sphere_form_factor(xd))
        ha = 1.0 if remove_attractor_form_factor else float(
            scaled_uniform_sphere_form_factor(xa)
        )
        exponent = -(r - radius_d_m - radius_a_m) / lambda_m
        scaled_kernel = hd * ha * np.exp(exponent)
        yp = G_SI * yukawa_amplitude * mass_d_kg * mass_a_kg
        yukawa_energy = -yukawa_sign * yp * scaled_kernel / r
        yukawa_derivative = (
            yukawa_sign
            * yp
            * scaled_kernel
            * (1.0 / r**2 + 1.0 / (lambda_m * r))
        )
    if component == "newtonian":
        return newton_energy, newton_derivative
    if component == "yukawa":
        return yukawa_energy, yukawa_derivative
    if component != "total":
        raise ValueError(f"unknown component: {component}")
    return newton_energy + yukawa_energy, newton_derivative + yukawa_derivative


def _pair_geometry(
    theta_rad: np.ndarray,
    gaps_m: np.ndarray,
    params: ApparatusParameters,
) -> tuple[
    np.ndarray,
    np.ndarray,
    np.ndarray,
    np.ndarray,
    np.ndarray,
    np.ndarray,
]:
    ld = LEVER_D + params.detector_lever_offset_m
    la = LEVER_A + params.attractor_lever_offset_m
    gaps = np.asarray(gaps_m, dtype=np.float64) + params.gap_offset_m
    if ld <= 0.0 or la <= 0.0 or np.any(gaps <= 0.0):
        raise ValueError("invalid perturbed lever arm or gap")
    theta = np.asarray(theta_rad, dtype=np.float64) - params.angular_zero_offset_rad
    th = theta.reshape((-1, 1, 1))
    gap_axis = gaps.reshape((1, -1, 1))
    s = np.asarray([-1.0, -1.0, 1.0, 1.0]).reshape((1, 1, 4))
    t = np.asarray([-1.0, 1.0, -1.0, 1.0]).reshape((1, 1, 4))
    detector_x = s * ld
    attractor_rot_x = t * la * np.cos(th)
    attractor_rot_y = t * la * np.sin(th)
    diff_x = (
        attractor_rot_x
        + params.attractor_axis_x_offset_m
        - detector_x
    )
    diff_y = attractor_rot_y + params.attractor_axis_y_offset_m
    diff_z = -(RADIUS_D + RADIUS_A + gap_axis)
    distance = np.sqrt(diff_x**2 + diff_y**2 + diff_z**2)
    d_attractor_x = -t * la * np.sin(th)
    d_attractor_y = t * la * np.cos(th)
    dr_dtheta = (diff_x * d_attractor_x + diff_y * d_attractor_y) / distance
    return distance, dr_dtheta, diff_x, diff_y, d_attractor_x, d_attractor_y


def apparatus_energy(
    theta_rad: np.ndarray,
    gaps_m: np.ndarray,
    lambda_m: float,
    params: ApparatusParameters = ApparatusParameters(),
    *,
    component: str = "total",
    yukawa_amplitude: float = A_Y,
    yukawa_sign: float = 1.0,
    remove_attractor_form_factor: bool = False,
) -> np.ndarray:
    distance, _, _, _, _, _ = _pair_geometry(theta_rad, gaps_m, params)
    mass_d = sphere_mass(RADIUS_D, DENSITY * (1.0 + params.detector_density_scale))
    mass_a = sphere_mass(RADIUS_A, DENSITY * (1.0 + params.source_density_scale))
    if mass_d <= 0.0 or mass_a <= 0.0:
        raise ValueError("invalid perturbed density")
    energy, _ = pair_energy_and_radial_derivative(
        distance,
        lambda_m,
        mass_d_kg=mass_d,
        mass_a_kg=mass_a,
        yukawa_amplitude=yukawa_amplitude,
        component=component,
        yukawa_sign=yukawa_sign,
        remove_attractor_form_factor=remove_attractor_form_factor,
    )
    return np.sum(energy, axis=2)


def analytic_energy_derivative_torque(
    theta_rad: np.ndarray,
    gaps_m: np.ndarray,
    lambda_m: float,
    params: ApparatusParameters = ApparatusParameters(),
    *,
    component: str = "total",
    yukawa_amplitude: float = A_Y,
    yukawa_sign: float = 1.0,
    remove_attractor_form_factor: bool = False,
    torque_sign: float = 1.0,
) -> np.ndarray:
    distance, dr_dtheta, _, _, _, _ = _pair_geometry(theta_rad, gaps_m, params)
    mass_d = sphere_mass(RADIUS_D, DENSITY * (1.0 + params.detector_density_scale))
    mass_a = sphere_mass(RADIUS_A, DENSITY * (1.0 + params.source_density_scale))
    _, derivative = pair_energy_and_radial_derivative(
        distance,
        lambda_m,
        mass_d_kg=mass_d,
        mass_a_kg=mass_a,
        yukawa_amplitude=yukawa_amplitude,
        component=component,
        yukawa_sign=yukawa_sign,
        remove_attractor_form_factor=remove_attractor_form_factor,
    )
    torque = -torque_sign * np.sum(derivative * dr_dtheta, axis=2)
    return torque * (1.0 + params.torque_calibration)


def direct_pair_force_lever_torque(
    theta_rad: np.ndarray,
    gaps_m: np.ndarray,
    lambda_m: float,
    params: ApparatusParameters = ApparatusParameters(),
    *,
    component: str = "total",
) -> np.ndarray:
    distance, _, diff_x, diff_y, d_attractor_x, d_attractor_y = _pair_geometry(
        theta_rad, gaps_m, params
    )
    mass_d = sphere_mass(RADIUS_D, DENSITY * (1.0 + params.detector_density_scale))
    mass_a = sphere_mass(RADIUS_A, DENSITY * (1.0 + params.source_density_scale))
    _, derivative = pair_energy_and_radial_derivative(
        distance,
        lambda_m,
        mass_d_kg=mass_d,
        mass_a_kg=mass_a,
        component=component,
    )
    force_x = -derivative * diff_x / distance
    force_y = -derivative * diff_y / distance
    generalized_torque = force_x * d_attractor_x + force_y * d_attractor_y
    return np.sum(generalized_torque, axis=2) * (1.0 + params.torque_calibration)


def five_point_energy_derivative_torque(
    theta_rad: np.ndarray,
    gaps_m: np.ndarray,
    lambda_m: float,
    step_rad: float,
    params: ApparatusParameters = ApparatusParameters(),
) -> np.ndarray:
    theta = np.asarray(theta_rad, dtype=np.float64)
    fm2 = apparatus_energy(theta - 2.0 * step_rad, gaps_m, lambda_m, params)
    fm1 = apparatus_energy(theta - step_rad, gaps_m, lambda_m, params)
    fp1 = apparatus_energy(theta + step_rad, gaps_m, lambda_m, params)
    fp2 = apparatus_energy(theta + 2.0 * step_rad, gaps_m, lambda_m, params)
    derivative = (fm2 - 8.0 * fm1 + 8.0 * fp1 - fp2) / (12.0 * step_rad)
    return -derivative * (1.0 + params.torque_calibration)


def discrete_harmonic_transform(
    torque_nm: np.ndarray,
    theta_rad: np.ndarray,
    harmonics: Iterable[int] = HARMONICS,
    *,
    normalization_multiplier: float = 1.0,
) -> np.ndarray:
    torque = np.asarray(torque_nm, dtype=np.float64)
    theta = np.asarray(theta_rad, dtype=np.float64)
    hs = np.asarray(tuple(harmonics), dtype=np.int64)
    phase = np.exp(-1j * theta.reshape((-1, 1)) * hs.reshape((1, -1)))
    return normalization_multiplier * (torque.T @ phase) / float(theta.size)


def _apply_harmonic_postprocessing(
    coefficients: np.ndarray,
    params: ApparatusParameters,
) -> np.ndarray:
    z = np.asarray(coefficients, dtype=np.complex128).copy()
    if params.harmonic_leakage != 0.0:
        leakage = np.asarray(
            [[0.0, 1.0, 0.0], [1.0, 0.0, 1.0], [0.0, 1.0, 0.0]],
            dtype=np.float64,
        )
        z = z + params.harmonic_leakage * (z @ leakage.T)
    for component_index, value in enumerate(params.backgrounds_nm):
        harmonic_index = component_index // 2
        if component_index % 2 == 0:
            z[:, harmonic_index] += value
        else:
            z[:, harmonic_index] += 1j * value
    return z


def real_150_vector_from_coefficients(coefficients: np.ndarray) -> np.ndarray:
    z = np.asarray(coefficients, dtype=np.complex128)
    if z.shape != (25, 3):
        raise ValueError(f"expected 25x3 coefficients, received {z.shape}")
    out = np.empty((25, 6), dtype=np.float64)
    out[:, 0::2] = z.real
    out[:, 1::2] = z.imag
    return out.reshape(150)


def real_150_vector(
    lambda_m: float,
    params: ApparatusParameters = ApparatusParameters(),
    *,
    angular_samples: int = 256,
    component: str = "total",
    yukawa_amplitude: float = A_Y,
    yukawa_sign: float = 1.0,
    remove_attractor_form_factor: bool = False,
    torque_sign: float = 1.0,
    normalization_multiplier: float = 1.0,
) -> tuple[np.ndarray, np.ndarray]:
    theta = 2.0 * math.pi * np.arange(angular_samples, dtype=np.float64) / angular_samples
    torque = analytic_energy_derivative_torque(
        theta,
        GAPS,
        lambda_m,
        params,
        component=component,
        yukawa_amplitude=yukawa_amplitude,
        yukawa_sign=yukawa_sign,
        remove_attractor_form_factor=remove_attractor_form_factor,
        torque_sign=torque_sign,
    )
    coefficients = discrete_harmonic_transform(
        torque,
        theta,
        normalization_multiplier=normalization_multiplier,
    )
    coefficients = _apply_harmonic_postprocessing(coefficients, params)
    vector = real_150_vector_from_coefficients(coefficients)
    if vector.shape != (150,) or not np.all(np.isfinite(vector)):
        raise ValueError("production vector is not a finite real-150 vector")
    return vector, coefficients


def reduced_four_dimensional_density_integral_yukawa_energy(
    center_distance_m: float,
    lambda_m: float,
    order: int,
    *,
    density_d_kg_m3: float = DENSITY,
    density_a_kg_m3: float = DENSITY,
) -> float:
    nodes, weights = leggauss(order)
    rd = 0.5 * RADIUS_D * (nodes + 1.0)
    wd = 0.5 * RADIUS_D * weights
    ra = 0.5 * RADIUS_A * (nodes + 1.0)
    wa = 0.5 * RADIUS_A * weights
    mu = nodes
    wmu = weights
    rd_grid = rd.reshape((-1, 1))
    mud_grid = mu.reshape((1, -1))
    inner_weight = (wd * rd**2).reshape((-1, 1)) * wmu.reshape((1, -1))
    total = 0.0
    for ra_value, wa_value in zip(ra, wa, strict=True):
        for mua_value, wmua_value in zip(mu, wmu, strict=True):
            distance_from_d_center = math.sqrt(
                center_distance_m**2
                + ra_value**2
                + 2.0 * center_distance_m * ra_value * mua_value
            )
            point_distance = np.sqrt(
                distance_from_d_center**2
                + rd_grid**2
                - 2.0 * distance_from_d_center * rd_grid * mud_grid
            )
            kernel = np.exp(-point_distance / lambda_m) / point_distance
            inner = float(np.sum(inner_weight * kernel))
            total += wa_value * ra_value**2 * wmua_value * inner
    density_integral = (2.0 * math.pi) ** 2 * density_d_kg_m3 * density_a_kg_m3 * total
    return -G_SI * A_Y * density_integral


def params_for_coordinate(parameter_id: str, q_value: float) -> ApparatusParameters:
    if parameter_id == "LOG_LAMBDA":
        raise ValueError("log lambda is not an apparatus parameter")
    physical = SCALES[parameter_id] * q_value
    kwargs: dict[str, Any] = {}
    mapping = {
        "TORQUE_CALIBRATION": "torque_calibration",
        "SOURCE_DENSITY_SCALE": "source_density_scale",
        "DETECTOR_DENSITY_SCALE": "detector_density_scale",
        "DETECTOR_LEVER_OFFSET": "detector_lever_offset_m",
        "ATTRACTOR_LEVER_OFFSET": "attractor_lever_offset_m",
        "GAP_OFFSET": "gap_offset_m",
        "ATTRACTOR_AXIS_X_OFFSET": "attractor_axis_x_offset_m",
        "ATTRACTOR_AXIS_Y_OFFSET": "attractor_axis_y_offset_m",
        "ANGULAR_ZERO_OFFSET": "angular_zero_offset_rad",
        "HARMONIC_LEAKAGE": "harmonic_leakage",
    }
    if parameter_id in mapping:
        kwargs[mapping[parameter_id]] = physical
    elif parameter_id in BACKGROUND_INDEX:
        backgrounds = [0.0] * 6
        backgrounds[BACKGROUND_INDEX[parameter_id]] = physical
        kwargs["backgrounds_nm"] = tuple(backgrounds)
    else:
        raise ValueError(f"unknown apparatus parameter: {parameter_id}")
    return ApparatusParameters(**kwargs)


def _rms(values: np.ndarray) -> float:
    return float(np.sqrt(np.mean(np.asarray(values, dtype=np.float64) ** 2)))


def build_dimensionless_jacobian(
    lambda_m: float,
    *,
    angular_samples: int,
    step_ladder: tuple[float, ...] = (1e-2, 3e-3, 1e-3),
    deterministic_noise_amplitude_y_star: float = 0.0,
) -> dict[str, Any]:
    newtonian, _ = real_150_vector(0.0, angular_samples=angular_samples, component="newtonian")
    y_star = float(np.max(np.abs(newtonian)))
    if y_star <= 1e-30:
        raise ValueError("accepted global output scale is below its fail floor")
    base, base_coefficients = real_150_vector(lambda_m, angular_samples=angular_samples)
    pattern = np.where(np.arange(150) % 2 == 0, 1.0, -1.0)
    derivative_by_parameter: dict[str, np.ndarray] = {}
    plateau_rows: list[dict[str, Any]] = []
    derivative_ladders: dict[str, list[np.ndarray]] = {}
    for parameter_id in FINITE_DIFFERENCE_COLUMNS:
        derivatives: list[np.ndarray] = []
        for h in step_ladder:
            if parameter_id == "LOG_LAMBDA":
                plus, _ = real_150_vector(
                    lambda_m * math.exp(h), angular_samples=angular_samples
                )
                minus, _ = real_150_vector(
                    lambda_m * math.exp(-h), angular_samples=angular_samples
                )
            else:
                plus, _ = real_150_vector(
                    lambda_m,
                    params_for_coordinate(parameter_id, h),
                    angular_samples=angular_samples,
                )
                minus, _ = real_150_vector(
                    lambda_m,
                    params_for_coordinate(parameter_id, -h),
                    angular_samples=angular_samples,
                )
            if deterministic_noise_amplitude_y_star != 0.0:
                noise = deterministic_noise_amplitude_y_star * y_star * pattern
                plus = plus + noise
                minus = minus - noise
            derivatives.append((plus - minus) / (2.0 * h))
        if len(derivatives) < 2:
            plateau_pass = False
            lhs = math.inf
            rhs = 0.0
        else:
            coarse_fine = derivatives[-2]
            fine = derivatives[-1]
            lhs = _rms((coarse_fine - fine) / y_star)
            rhs = 1e-10 + 5e-3 * _rms(fine / y_star)
            plateau_pass = lhs <= rhs
        derivative_by_parameter[parameter_id] = derivatives[-1]
        derivative_ladders[parameter_id] = derivatives
        plateau_rows.append(
            {
                "parameter_id": parameter_id,
                "lhs_scaled_rms": lhs,
                "rhs_tolerance": rhs,
                "pass": plateau_pass,
            }
        )

    derivative_by_parameter["TORQUE_CALIBRATION"] = (
        SCALES["TORQUE_CALIBRATION"] * base
    )
    derivative_by_parameter["SOURCE_DENSITY_SCALE"] = (
        SCALES["SOURCE_DENSITY_SCALE"] * base
    )
    derivative_by_parameter["DETECTOR_DENSITY_SCALE"] = (
        SCALES["DETECTOR_DENSITY_SCALE"] * base
    )
    leakage_matrix = np.asarray(
        [[0.0, 1.0, 0.0], [1.0, 0.0, 1.0], [0.0, 1.0, 0.0]], dtype=np.float64
    )
    leakage_coefficients = SCALES["HARMONIC_LEAKAGE"] * (
        base_coefficients @ leakage_matrix.T
    )
    derivative_by_parameter["HARMONIC_LEAKAGE"] = (
        real_150_vector_from_coefficients(leakage_coefficients)
    )
    for background_id, component_index in BACKGROUND_INDEX.items():
        column = np.zeros((25, 6), dtype=np.float64)
        column[:, component_index] = SCALES[background_id]
        derivative_by_parameter[background_id] = column.reshape(150)

    jacobian = np.column_stack(
        [derivative_by_parameter[parameter_id] for parameter_id in PARAMETER_ORDER]
    )
    if jacobian.shape != (150, 17) or not np.all(np.isfinite(jacobian)):
        raise ValueError("Jacobian is not finite real 150x17")
    return {
        "base_vector": base,
        "base_coefficients": base_coefficients,
        "newtonian_vector": newtonian,
        "y_star": y_star,
        "jacobian": jacobian,
        "plateau_rows": plateau_rows,
        "plateau_pass": all(row["pass"] for row in plateau_rows),
        "derivative_ladders": derivative_ladders,
    }


def analyze_scaled_jacobian(
    jacobian: np.ndarray,
    y_star: float,
    *,
    rank_threshold: float,
) -> dict[str, Any]:
    scaled = np.asarray(jacobian, dtype=np.float64) / y_star
    scalar = scaled[:, 0]
    nuisance = scaled[:, 1:]
    nuisance_norms = np.linalg.norm(nuisance, axis=0)
    zero_floor = math.sqrt(150.0) * 1e-12
    nonzero = np.flatnonzero(nuisance_norms > zero_floor)
    zero = np.flatnonzero(nuisance_norms <= zero_floor)
    if nonzero.size == 0:
        nuisance_unit = np.empty((150, 0), dtype=np.float64)
        u = np.empty((150, 0), dtype=np.float64)
        singular_values = np.empty((0,), dtype=np.float64)
        vt = np.empty((0, 0), dtype=np.float64)
        rank = 0
        ur = u
    else:
        nuisance_unit = nuisance[:, nonzero] / nuisance_norms[nonzero]
        u, singular_values, vt = np.linalg.svd(nuisance_unit, full_matrices=False)
        rank = int(np.sum((singular_values / singular_values[0]) > rank_threshold))
        ur = u[:, :rank]
    if rank == 0:
        projected = np.zeros_like(scalar)
        pseudoinverse = np.zeros((nuisance_unit.shape[1], 150), dtype=np.float64)
        orthonormality_residual = 0.0
    else:
        projected = ur @ (ur.T @ scalar)
        vr = vt[:rank, :].T
        pseudoinverse = vr @ np.diag(1.0 / singular_values[:rank]) @ ur.T
        orthonormality_residual = float(
            np.linalg.norm(ur.T @ ur - np.eye(rank), ord=2)
        )
    scalar_norm = float(np.linalg.norm(scalar))
    scalar_zero = scalar_norm <= zero_floor
    residual = scalar - projected
    eta = 0.0 if scalar_zero else float(np.linalg.norm(residual) / scalar_norm)
    if scalar_zero:
        classification = "IDENTIFIABILITY_CLASSIFICATION_UNRESOLVED"
    elif eta <= 1e-6:
        classification = "INDISTINGUISHABLE_AT_POINT"
    elif eta >= 1e-3:
        classification = "IDENTIFIABLE_AT_POINT"
    else:
        classification = "IDENTIFIABILITY_CLASSIFICATION_UNRESOLVED"
    if nuisance_unit.shape[1] == 0:
        reconstruction_residual = 0.0
    else:
        reconstruction_residual = float(
            np.linalg.norm(nuisance_unit - ur @ (ur.T @ nuisance_unit), ord="fro")
            / max(float(np.linalg.norm(nuisance_unit, ord="fro")), 1e-30)
        )
    correlations = np.zeros(16, dtype=np.float64)
    for index in range(16):
        if nuisance_norms[index] > zero_floor and scalar_norm > zero_floor:
            correlations[index] = float(
                np.dot(scalar, nuisance[:, index])
                / (scalar_norm * nuisance_norms[index])
            )
    exact_pairs: list[tuple[str, str]] = []
    near_pairs: list[tuple[str, str]] = []
    for left in range(16):
        for right in range(left + 1, 16):
            if nuisance_norms[left] <= zero_floor or nuisance_norms[right] <= zero_floor:
                continue
            correlation = float(
                np.dot(nuisance[:, left], nuisance[:, right])
                / (nuisance_norms[left] * nuisance_norms[right])
            )
            residual_fraction = math.sqrt(max(0.0, 1.0 - min(1.0, correlation**2)))
            pair = (PARAMETER_ORDER[left + 1], PARAMETER_ORDER[right + 1])
            if residual_fraction <= 1e-10:
                exact_pairs.append(pair)
            elif abs(correlation) >= 0.999:
                near_pairs.append(pair)
    condition_number = (
        1.0
        if rank <= 1
        else float(singular_values[0] / singular_values[rank - 1])
    )
    projector_valid = (
        orthonormality_residual <= 1e-12
        and reconstruction_residual <= 1e-9
        and np.all(np.isfinite(pseudoinverse))
    )
    return {
        "rank_threshold": rank_threshold,
        "rank": rank,
        "singular_values": singular_values,
        "u_retained": ur,
        "pseudoinverse": pseudoinverse,
        "zero_nuisance_indices": zero,
        "nonzero_nuisance_indices": nonzero,
        "nuisance_norms": nuisance_norms,
        "scalar_norm": scalar_norm,
        "scalar_zero": scalar_zero,
        "eta": eta,
        "classification": classification,
        "correlations": correlations,
        "max_abs_correlation": float(np.max(np.abs(correlations))),
        "exact_pairs": exact_pairs,
        "near_pairs": near_pairs,
        "condition_number": condition_number,
        "orthonormality_residual": orthonormality_residual,
        "reconstruction_residual": reconstruction_residual,
        "projector_valid": projector_valid,
    }


def principal_angle_degrees(u_left: np.ndarray, u_right: np.ndarray) -> float:
    if u_left.shape[1] != u_right.shape[1]:
        return math.inf
    if u_left.shape[1] == 0:
        return 0.0
    singular = np.linalg.svd(u_left.T @ u_right, compute_uv=False)
    cosine = float(np.clip(np.min(singular), -1.0, 1.0))
    return math.degrees(math.acos(cosine))


def compare_identifiability_refinements(
    medium: dict[str, Any],
    fine: dict[str, Any],
) -> dict[str, Any]:
    rank_equal = medium["rank"] == fine["rank"]
    eta_abs = abs(medium["eta"] - fine["eta"])
    eta_scale = max(abs(medium["eta"]), abs(fine["eta"]))
    eta_rel = 0.0 if eta_scale <= 1e-6 else eta_abs / eta_scale
    correlation_change = abs(
        medium["max_abs_correlation"] - fine["max_abs_correlation"]
    )
    angle = principal_angle_degrees(medium["u_retained"], fine["u_retained"])
    if rank_equal and medium["rank"] > 0:
        count = medium["rank"]
        log_singular_change = float(
            np.max(
                np.abs(
                    np.log10(medium["singular_values"][:count])
                    - np.log10(fine["singular_values"][:count])
                )
            )
        )
    else:
        log_singular_change = math.inf if not rank_equal else 0.0
    labels_equal = (
        medium["exact_pairs"] == fine["exact_pairs"]
        and medium["near_pairs"] == fine["near_pairs"]
    )
    classification_equal = medium["classification"] == fine["classification"]
    passed = (
        rank_equal
        and eta_abs <= 0.02
        and (eta_scale <= 1e-6 or eta_rel <= 0.05)
        and correlation_change <= 0.02
        and angle <= 1.0
        and log_singular_change <= 0.05
        and labels_equal
        and classification_equal
        and medium["projector_valid"]
        and fine["projector_valid"]
    )
    return {
        "rank_equal": rank_equal,
        "eta_absolute_change": eta_abs,
        "eta_relative_change": eta_rel,
        "correlation_absolute_change": correlation_change,
        "principal_angle_degrees": angle,
        "log10_singular_value_change_decades": log_singular_change,
        "degeneracy_labels_equal": labels_equal,
        "classification_equal": classification_equal,
        "pass": passed,
    }
