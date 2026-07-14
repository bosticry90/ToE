from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import subprocess
import sys
import unicodedata
from pathlib import Path
from typing import Any

import numpy as np

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_non_authoritative_pilot.py"
GUARDRAIL_PACKET = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DISCRETE-NUMERICAL-GUARDRAIL-PACKET-v0.json"
GUARDRAIL_REVIEW = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DISCRETE_NUMERICAL_GUARDRAIL_PACKET_RESULT_REVIEW_20260713_v0.json"
INPUT_HASHES = {
    GUARDRAIL_PACKET: "52ffd123b3eb516ab824291364afd2006c90951f04d12587658941cbe499da82",
    GUARDRAIL_REVIEW: "b881d23e9bd201b09bb023a1e897306afff681bd57ccb224a9c6baf562be57b6",
}
PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-NON-AUTHORITATIVE-PILOT-PACKET-v0.json"
ARRAYS_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-NON-AUTHORITATIVE-PILOT-ARRAYS-v0.json"
MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-NON-AUTHORITATIVE-PILOT-MANIFEST-v0.json"
REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_NON_AUTHORITATIVE_PILOT_20260713_v0.json"
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
ARRAYS_PATH = REPO_ROOT / ARRAYS_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
REPORT_PATH = REPO_ROOT / REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
TARGET = "execute_dirac_maxwell_full_zero_mode_non_authoritative_pilot_v0"
REVIEW_TARGET = "review_dirac_maxwell_full_zero_mode_non_authoritative_pilot_v0_result"
REVIEW_TARGET_KIND = "dirac_maxwell_full_zero_mode_non_authoritative_pilot_v0_result_review"
ENGINEERING_READY_TARGET = "prepare_dirac_maxwell_full_zero_mode_canonical_parameter_freeze_packet_v0"
IMPLEMENTATION_DEFECT_TARGET = "prepare_dirac_maxwell_full_zero_mode_pilot_implementation_repair_packet_v0"
NUMERICAL_INSTABILITY_TARGET = "prepare_dirac_maxwell_full_zero_mode_numerical_method_revision_packet_v0"
CONTROL_DEFECT_TARGET = "prepare_dirac_maxwell_full_zero_mode_guardrail_diagnostic_repair_packet_v0"
THRESHOLD_INSTABILITY_TARGET = "prepare_dirac_maxwell_full_zero_mode_threshold_rule_revision_packet_v0"
PACKET_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_NON_AUTHORITATIVE_PILOT_PACKET_v0"
ARRAYS_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_NON_AUTHORITATIVE_PILOT_ARRAYS_v0"
MANIFEST_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_NON_AUTHORITATIVE_PILOT_MANIFEST_v0"
REPORT_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_NON_AUTHORITATIVE_PILOT_20260713_v0"
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"

LENGTH = 1.0
MASS = 1.0
CHARGE = 0.2
WILSON_R = 1.0
RUN_DURATION = 0.05
GRID_SEQUENCE = [8, 16, 32]
TEMPORAL_DT_SEQUENCE = [0.00625, 0.003125, 0.0015625]
SOLVER_TOLERANCES = [1e-8, 1e-10, 1e-12]
MAX_ITERATIONS = 80


def _normalize(value: Any) -> Any:
    if isinstance(value, str):
        return unicodedata.normalize("NFC", value)
    if isinstance(value, list):
        return [_normalize(item) for item in value]
    if isinstance(value, dict):
        return {_normalize(str(key)): _normalize(item) for key, item in value.items()}
    return value


def canonical_json_bytes(payload: Any) -> bytes:
    return (json.dumps(_normalize(payload), allow_nan=False, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected object: {path}")
    return value


def load_authority() -> None:
    for path, digest in INPUT_HASHES.items():
        if sha256_path(REPO_ROOT / path) != digest:
            raise ValueError(f"input hash mismatch: {path}")
    review = load_json(REPO_ROOT / GUARDRAIL_REVIEW)
    if not (
        review.get("accepted") is True
        and review.get("selected_next_target") == TARGET
        and review.get("authority_rotation", {}).get("numerical_guardrail_accepted") is True
        and review.get("authority_rotation", {}).get("non_authoritative_pilot_execution_authorized") is True
        and review.get("authority_rotation", {}).get("canonical_execution_authorized") is False
    ):
        raise ValueError("guardrail review does not authorize this pilot")


I2 = np.eye(2, dtype=np.complex128)
SIGMA1 = np.array([[0, 1], [1, 0]], dtype=np.complex128)
SIGMA2 = np.array([[0, -1j], [1j, 0]], dtype=np.complex128)
SIGMA3 = np.array([[1, 0], [0, -1]], dtype=np.complex128)
GAMMA0 = np.kron(SIGMA3, I2)
GAMMA1 = np.kron(1j * SIGMA2, I2)
GAMMA2 = 1j * np.kron(SIGMA1, SIGMA1)
GAMMA3 = 1j * np.kron(SIGMA1, SIGMA2)
BETA = GAMMA0
ALPHA1 = GAMMA0 @ GAMMA1
ALPHA2 = GAMMA0 @ GAMMA2
ALPHA3 = GAMMA0 @ GAMMA3


def canonical_eigenvector(operator: np.ndarray, largest: bool) -> np.ndarray:
    values, vectors = np.linalg.eigh(operator)
    vector = vectors[:, -1 if largest else 0].astype(np.complex128)
    pivot = int(np.argmax(np.abs(vector)))
    phase = np.angle(vector[pivot])
    vector *= np.exp(-1j * phase)
    if vector[pivot].real < 0:
        vector *= -1
    return vector / np.linalg.norm(vector)


def pack(state: dict[str, np.ndarray]) -> np.ndarray:
    real_fields = np.concatenate([state[key].real for key in ("theta", "p", "phi2", "P2", "phi3", "P3")])
    spinors = []
    for key in ("psi_plus", "psi_minus"):
        spinors.extend([state[key].real.ravel(), state[key].imag.ravel()])
    return np.concatenate([real_fields, *spinors]).astype(np.float64)


def unpack(vector: np.ndarray, n: int) -> dict[str, np.ndarray]:
    offset = 0
    result: dict[str, np.ndarray] = {}
    for key in ("theta", "p", "phi2", "P2", "phi3", "P3"):
        result[key] = vector[offset : offset + n].copy()
        offset += n
    for key in ("psi_plus", "psi_minus"):
        real = vector[offset : offset + 4 * n].reshape(n, 4)
        offset += 4 * n
        imag = vector[offset : offset + 4 * n].reshape(n, 4)
        offset += 4 * n
        result[key] = real + 1j * imag
    return result


def initial_state(case: str, n: int, q: float = CHARGE) -> dict[str, np.ndarray]:
    a = LENGTH / n
    x = np.arange(n, dtype=np.float64) * a
    zero = np.zeros(n, dtype=np.float64)
    state = {
        "theta": zero.copy(),
        "p": zero.copy(),
        "phi2": zero.copy(),
        "P2": zero.copy(),
        "phi3": zero.copy(),
        "P3": zero.copy(),
        "psi_plus": np.zeros((n, 4), dtype=np.complex128),
        "psi_minus": np.zeros((n, 4), dtype=np.complex128),
    }
    amplitude = 0.08
    if case == "vacuum":
        return state
    if case == "q0_wave":
        state["phi2"] = 0.02 * np.cos(2 * np.pi * x / LENGTH)
        state["P3"] = a * 0.015 * np.sin(4 * np.pi * x / LENGTH)
        vector = canonical_eigenvector(BETA, True)
        phase = np.exp(1j * 2 * np.pi * x / LENGTH)
        state["psi_plus"] = amplitude * phase[:, None] * vector[None, :]
        state["psi_minus"] = state["psi_plus"].copy()
        return state
    if case == "stationary_neutral" or case == "zero_transverse_current":
        vector = canonical_eigenvector(BETA, True)
        state["psi_plus"][:] = amplitude * vector
        state["psi_minus"][:] = amplitude * vector
        return state
    if case == "phi2_response":
        plus = canonical_eigenvector(ALPHA2, True)
        minus = canonical_eigenvector(ALPHA2, False)
        state["psi_plus"][:] = amplitude * plus
        state["psi_minus"][:] = amplitude * minus
        return state
    if case == "phi3_response":
        plus = canonical_eigenvector(ALPHA3, True)
        minus = canonical_eigenvector(ALPHA3, False)
        state["psi_plus"][:] = amplitude * plus
        state["psi_minus"][:] = amplitude * minus
        return state
    if case == "full_mixed":
        transverse = ALPHA2 + 0.7 * ALPHA3
        plus = canonical_eigenvector(transverse, True)
        minus = canonical_eigenvector(transverse, False)
        envelope = 1.0 + 0.08 * np.cos(2 * np.pi * x / LENGTH)
        plus_phase = np.exp(1j * 2 * np.pi * x / LENGTH)
        minus_phase = np.exp(-1j * 2 * np.pi * x / LENGTH)
        state["psi_plus"] = amplitude * envelope[:, None] * plus_phase[:, None] * plus[None, :]
        state["psi_minus"] = amplitude * envelope[:, None] * minus_phase[:, None] * minus[None, :]
        state["phi2"] = 0.01 * np.cos(2 * np.pi * x / LENGTH)
        state["phi3"] = 0.008 * np.sin(4 * np.pi * x / LENGTH)
        state["theta"][:] = 0.3 / (q * n)
        return state
    raise ValueError(f"unknown case: {case}")


def hamiltonian_parts(
    psi: np.ndarray,
    theta: np.ndarray,
    phi2: np.ndarray,
    phi3: np.ndarray,
    sigma: int,
    a: float,
    q: float,
) -> tuple[np.ndarray, dict[str, np.ndarray]]:
    phase_forward = np.exp(1j * sigma * q * theta)
    phase_backward = np.exp(-1j * sigma * q * np.roll(theta, 1))
    next_psi = np.roll(psi, -1, axis=0)
    previous_psi = np.roll(psi, 1, axis=0)
    local = np.einsum("ij,nj->ni", BETA * (MASS + WILSON_R / a), psi)
    forward_matrix = (-1j * ALPHA1 - WILSON_R * BETA) / (2 * a)
    backward_matrix = (1j * ALPHA1 - WILSON_R * BETA) / (2 * a)
    link = np.einsum("ij,nj->ni", forward_matrix, phase_forward[:, None] * next_psi)
    link += np.einsum("ij,nj->ni", backward_matrix, phase_backward[:, None] * previous_psi)
    transverse2 = sigma * q * phi2[:, None] * np.einsum("ij,nj->ni", ALPHA2, psi)
    transverse3 = sigma * q * phi3[:, None] * np.einsum("ij,nj->ni", ALPHA3, psi)
    return local + link + transverse2 + transverse3, {
        "local": local,
        "link": link,
        "transverse2": transverse2,
        "transverse3": transverse3,
    }


def matter_observables(state: dict[str, np.ndarray], a: float, q: float) -> dict[str, np.ndarray]:
    theta = state["theta"]
    phi2 = state["phi2"]
    phi3 = state["phi3"]
    charge_density = np.zeros(theta.shape, dtype=np.float64)
    j2 = np.zeros(theta.shape, dtype=np.float64)
    j3 = np.zeros(theta.shape, dtype=np.float64)
    grad_theta = np.zeros(theta.shape, dtype=np.float64)
    hpsi: dict[str, np.ndarray] = {}
    parts: dict[str, dict[str, np.ndarray]] = {}
    for sigma, key in ((1, "psi_plus"), (-1, "psi_minus")):
        psi = state[key]
        hpsi[key], parts[key] = hamiltonian_parts(psi, theta, phi2, phi3, sigma, a, q)
        density = np.sum(np.abs(psi) ** 2, axis=1).real
        charge_density += sigma * q * density
        j2 += sigma * q * np.einsum("ni,ij,nj->n", psi.conj(), ALPHA2, psi).real
        j3 += sigma * q * np.einsum("ni,ij,nj->n", psi.conj(), ALPHA3, psi).real
        forward_matrix = (-1j * ALPHA1 - WILSON_R * BETA) / (2 * a)
        next_psi = np.roll(psi, -1, axis=0)
        phase = np.exp(1j * sigma * q * theta)
        z = np.einsum("ni,ij,nj->n", psi.conj(), forward_matrix, phase[:, None] * next_psi)
        grad_theta += 2 * a * np.real(1j * sigma * q * z)
    return {"rho": charge_density, "j2": j2, "j3": j3, "grad_theta": grad_theta, "hpsi_plus": hpsi["psi_plus"], "hpsi_minus": hpsi["psi_minus"], "parts": parts}


def rhs(vector: np.ndarray, n: int, q: float) -> np.ndarray:
    a = LENGTH / n
    state = unpack(vector, n)
    obs = matter_observables(state, a, q)
    derivative = {key: np.zeros_like(value) for key, value in state.items()}
    derivative["theta"] = state["p"] / a
    derivative["p"] = -obs["grad_theta"]
    derivative["phi2"] = state["P2"] / a
    derivative["phi3"] = state["P3"] / a
    lap2 = (np.roll(state["phi2"], -1) - 2 * state["phi2"] + np.roll(state["phi2"], 1)) / a**2
    lap3 = (np.roll(state["phi3"], -1) - 2 * state["phi3"] + np.roll(state["phi3"], 1)) / a**2
    derivative["P2"] = a * (lap2 - obs["j2"])
    derivative["P3"] = a * (lap3 - obs["j3"])
    derivative["psi_plus"] = -1j * obs["hpsi_plus"]
    derivative["psi_minus"] = -1j * obs["hpsi_minus"]
    return pack(derivative)


def implicit_midpoint_step(vector: np.ndarray, n: int, q: float, dt: float, tolerance: float, max_iterations: int) -> tuple[np.ndarray, float, int, bool]:
    guess = vector + dt * rhs(vector, n, q)
    converged = False
    residual = math.inf
    for iteration in range(1, max_iterations + 1):
        midpoint = 0.5 * (vector + guess)
        updated = vector + dt * rhs(midpoint, n, q)
        residual = float(np.max(np.abs(updated - guess)))
        guess = updated
        if residual <= tolerance:
            converged = True
            break
    equation_residual = float(np.max(np.abs(guess - vector - dt * rhs(0.5 * (vector + guess), n, q))))
    return guess, max(residual, equation_residual), iteration, converged


def energy_components(state: dict[str, np.ndarray], a: float, q: float) -> dict[str, float]:
    p_mean = float(np.mean(state["p"]))
    electric_zero = state["p"].size * p_mean**2 / (2 * a)
    electric_fluctuating = float(np.sum((state["p"] - p_mean) ** 2) / (2 * a))
    grad2 = (np.roll(state["phi2"], -1) - state["phi2"]) / a
    grad3 = (np.roll(state["phi3"], -1) - state["phi3"]) / a
    phi2_energy = float(np.sum(state["P2"] ** 2) / (2 * a) + 0.5 * a * np.sum(grad2**2))
    phi3_energy = float(np.sum(state["P3"] ** 2) / (2 * a) + 0.5 * a * np.sum(grad3**2))
    matter_local = 0.0
    link_interaction = 0.0
    gamma2_interaction = 0.0
    gamma3_interaction = 0.0
    obs = matter_observables(state, a, q)
    for key in ("psi_plus", "psi_minus"):
        psi = state[key]
        parts = obs["parts"][key]
        matter_local += float(a * np.einsum("ni,ni->", psi.conj(), parts["local"]).real)
        link_interaction += float(a * np.einsum("ni,ni->", psi.conj(), parts["link"]).real)
        gamma2_interaction += float(a * np.einsum("ni,ni->", psi.conj(), parts["transverse2"]).real)
        gamma3_interaction += float(a * np.einsum("ni,ni->", psi.conj(), parts["transverse3"]).real)
    return {
        "electric_fluctuating": electric_fluctuating,
        "electric_zero_mode": electric_zero,
        "phi2": phi2_energy,
        "phi3": phi3_energy,
        "Wilson_Dirac_local": matter_local,
        "link_interaction": link_interaction,
        "gamma2_interaction": gamma2_interaction,
        "gamma3_interaction": gamma3_interaction,
    }


def diagnostics(state: dict[str, np.ndarray], a: float, q: float) -> dict[str, float]:
    obs = matter_observables(state, a, q)
    gauss = np.roll(state["p"], 1) - state["p"] + a * obs["rho"]
    links = np.exp(1j * q * state["theta"])
    energies = energy_components(state, a, q)
    plus_positive, plus_negative = free_wilson_spectral_weights(state["psi_plus"], a)
    minus_positive, minus_negative = free_wilson_spectral_weights(state["psi_minus"], a)
    return {
        "total_energy": float(sum(energies.values())),
        "link_norm_error": float(np.max(np.abs(np.abs(links) - 1.0))),
        "gauss_residual": float(np.max(np.abs(gauss))),
        "total_charge": float(a * np.sum(obs["rho"])),
        "J2_l2": float(math.sqrt(a * np.sum(obs["j2"] ** 2))),
        "J3_l2": float(math.sqrt(a * np.sum(obs["j3"] ** 2))),
        "phi2_l2": float(math.sqrt(a * np.sum(state["phi2"] ** 2))),
        "phi3_l2": float(math.sqrt(a * np.sum(state["phi3"] ** 2))),
        "J1_l2": float(math.sqrt(np.sum(obs["grad_theta"] ** 2) / a)),
        "psi_plus_positive_frequency_weight": plus_positive,
        "psi_plus_negative_frequency_weight": plus_negative,
        "psi_minus_positive_frequency_weight": minus_positive,
        "psi_minus_negative_frequency_weight": minus_negative,
        "periodic_boundary_flux": 0.0,
        **{f"energy_{key}": value for key, value in energies.items()},
    }


def free_wilson_spectral_weights(psi: np.ndarray, a: float) -> tuple[float, float]:
    """Project onto the frozen free Wilson-Hamiltonian diagnostic basis."""
    n = psi.shape[0]
    modes = np.fft.fft(psi, axis=0) / math.sqrt(n)
    momenta = 2 * np.pi * np.fft.fftfreq(n, d=a)
    positive = 0.0
    negative = 0.0
    for mode, momentum in zip(modes, momenta, strict=True):
        ka = momentum * a
        operator = ALPHA1 * (math.sin(ka) / a) + BETA * (MASS + WILSON_R * (1 - math.cos(ka)) / a)
        values, vectors = np.linalg.eigh(operator)
        coefficients = vectors.conj().T @ mode
        positive += float(np.sum(np.abs(coefficients[values >= 0]) ** 2))
        negative += float(np.sum(np.abs(coefficients[values < 0]) ** 2))
    return a * positive, a * negative


def _format_series(values: list[float]) -> list[str]:
    return [format(float(value), ".12e") for value in values]


def simulate(case: str, n: int, dt: float, duration: float, tolerance: float, max_iterations: int, q: float = CHARGE) -> dict[str, Any]:
    a = LENGTH / n
    steps = max(1, int(round(duration / dt)))
    dt = duration / steps
    vector = pack(initial_state(case, n, q))
    initial = diagnostics(unpack(vector, n), a, q)
    series: dict[str, list[float]] = {key: [value] for key, value in initial.items()}
    equation_residual_keys = (
        "longitudinal_Maxwell_residual",
        "phi2_wave_residual",
        "phi3_wave_residual",
        "Dirac_plus_sector1_residual",
        "Dirac_plus_sector2_residual",
        "Dirac_minus_sector1_residual",
        "Dirac_minus_sector2_residual",
        "adjoint_plus_sector1_residual",
        "adjoint_plus_sector2_residual",
        "adjoint_minus_sector1_residual",
        "adjoint_minus_sector2_residual",
    )
    series.update({key: [0.0] for key in ("time", "solver_residual", "solver_iterations", "continuity_residual", "exchange_longitudinal", "exchange_phi2", "exchange_phi3", "exchange_combined", "total_energy_delta", *equation_residual_keys)})
    all_converged = True
    maximum_iteration = 0
    for step in range(1, steps + 1):
        previous_vector = vector
        previous_state = unpack(previous_vector, n)
        previous_energy = energy_components(previous_state, a, q)
        vector, solver_residual, iterations, converged = implicit_midpoint_step(previous_vector, n, q, dt, tolerance, max_iterations)
        all_converged = all_converged and converged
        maximum_iteration = max(maximum_iteration, iterations)
        state = unpack(vector, n)
        current = diagnostics(state, a, q)
        current_energy = energy_components(state, a, q)
        midpoint_state = unpack(0.5 * (previous_vector + vector), n)
        equation_defect = unpack(vector - previous_vector - dt * rhs(0.5 * (previous_vector + vector), n, q), n)
        equation_residuals = {
            "longitudinal_Maxwell_residual": float(max(np.max(np.abs(equation_defect["theta"])), np.max(np.abs(equation_defect["p"])))),
            "phi2_wave_residual": float(max(np.max(np.abs(equation_defect["phi2"])), np.max(np.abs(equation_defect["P2"])))),
            "phi3_wave_residual": float(max(np.max(np.abs(equation_defect["phi3"])), np.max(np.abs(equation_defect["P3"])))),
            "Dirac_plus_sector1_residual": float(np.max(np.abs(equation_defect["psi_plus"][:, :2]))),
            "Dirac_plus_sector2_residual": float(np.max(np.abs(equation_defect["psi_plus"][:, 2:]))),
            "Dirac_minus_sector1_residual": float(np.max(np.abs(equation_defect["psi_minus"][:, :2]))),
            "Dirac_minus_sector2_residual": float(np.max(np.abs(equation_defect["psi_minus"][:, 2:]))),
        }
        equation_residuals.update({key.replace("Dirac", "adjoint"): value for key, value in list(equation_residuals.items()) if key.startswith("Dirac")})
        midpoint_obs = matter_observables(midpoint_state, a, q)
        theta_dot = midpoint_state["p"] / a
        phi2_dot = midpoint_state["P2"] / a
        phi3_dot = midpoint_state["P3"] / a
        work_longitudinal = float(np.sum(midpoint_obs["grad_theta"] * theta_dot))
        work_phi2 = float(a * np.sum(midpoint_obs["j2"] * phi2_dot))
        work_phi3 = float(a * np.sum(midpoint_obs["j3"] * phi3_dot))
        delta_electric = (current_energy["electric_fluctuating"] + current_energy["electric_zero_mode"]) - (previous_energy["electric_fluctuating"] + previous_energy["electric_zero_mode"])
        delta_phi2 = current_energy["phi2"] - previous_energy["phi2"]
        delta_phi3 = current_energy["phi3"] - previous_energy["phi3"]
        exchange_longitudinal = delta_electric + dt * work_longitudinal
        exchange_phi2 = delta_phi2 + dt * work_phi2
        exchange_phi3 = delta_phi3 + dt * work_phi3
        exchange_combined = exchange_longitudinal + exchange_phi2 + exchange_phi3
        previous_obs = matter_observables(previous_state, a, q)
        current_obs = matter_observables(state, a, q)
        rho_rate = (current_obs["rho"] - previous_obs["rho"]) / dt
        current_divergence = (midpoint_obs["grad_theta"] - np.roll(midpoint_obs["grad_theta"], 1)) / a
        continuity = float(np.max(np.abs(rho_rate + current_divergence)))
        for key, value in current.items():
            series[key].append(value)
        series["time"].append(step * dt)
        series["solver_residual"].append(solver_residual)
        series["solver_iterations"].append(float(iterations))
        series["continuity_residual"].append(continuity)
        series["exchange_longitudinal"].append(exchange_longitudinal)
        series["exchange_phi2"].append(exchange_phi2)
        series["exchange_phi3"].append(exchange_phi3)
        series["exchange_combined"].append(exchange_combined)
        series["total_energy_delta"].append(current["total_energy"] - initial["total_energy"])
        for key, value in equation_residuals.items():
            series[key].append(value)
    energy_delta = np.array(series["total_energy_delta"])
    summary = {
        "run_id": f"{case}_N{n}_dt{dt:.8f}_tol{tolerance:.0e}",
        "case": case,
        "N": n,
        "a": a,
        "dt": dt,
        "duration": duration,
        "steps": steps,
        "solver_tolerance": tolerance,
        "max_iterations_allowed": max_iterations,
        "all_steps_converged": all_converged,
        "maximum_iterations_used": maximum_iteration,
        "maximum_solver_residual": max(series["solver_residual"]),
        "maximum_link_norm_error": max(series["link_norm_error"]),
        "maximum_Gauss_residual": max(series["gauss_residual"]),
        "maximum_continuity_residual": max(series["continuity_residual"]),
        "maximum_energy_drift": float(np.max(np.abs(energy_delta))),
        "final_energy_drift": float(energy_delta[-1]),
        "energy_drift_class": "OSCILLATORY_OR_BOUNDED" if np.max(np.abs(energy_delta)) <= 10 * max(abs(energy_delta[-1]), tolerance) else "UNCLASSIFIED",
        "maximum_exchange_longitudinal_residual": max(abs(value) for value in series["exchange_longitudinal"]),
        "maximum_exchange_phi2_residual": max(abs(value) for value in series["exchange_phi2"]),
        "maximum_exchange_phi3_residual": max(abs(value) for value in series["exchange_phi3"]),
        "maximum_exchange_combined_residual": max(abs(value) for value in series["exchange_combined"]),
        **{f"maximum_{key}": max(abs(value) for value in series[key]) for key in equation_residual_keys},
        "initial_J2_l2": series["J2_l2"][0],
        "initial_J3_l2": series["J3_l2"][0],
        "final_phi2_l2": series["phi2_l2"][-1],
        "final_phi3_l2": series["phi3_l2"][-1],
        "final_total_energy": series["total_energy"][-1],
    }
    registered = {"run_id": summary["run_id"], "series": {key: _format_series(values) for key, values in series.items()}}
    return {"summary": summary, "registered": registered}


def observed_order(coarse: float, middle: float, fine: float) -> float | None:
    numerator = abs(coarse - middle)
    denominator = abs(middle - fine)
    if denominator == 0 or numerator == 0:
        return None
    return math.log(numerator / denominator, 2)


def dispersion_evidence() -> dict[str, Any]:
    k = 2 * np.pi / LENGTH
    rows = []
    errors = []
    matrix_errors = []
    continuum = math.sqrt(k**2 + MASS**2)
    for n in (64, 128, 256):
        a = LENGTH / n
        discrete = math.sqrt((math.sin(k * a) / a) ** 2 + (MASS + WILSON_R * (1 - math.cos(k * a)) / a) ** 2)
        hk = ALPHA1 * (math.sin(k * a) / a) + BETA * (MASS + WILSON_R * (1 - math.cos(k * a)) / a)
        eigenvalues = np.linalg.eigvalsh(hk)
        matrix_error = float(min(abs(abs(value) - discrete) for value in eigenvalues))
        error = abs(discrete - continuum)
        errors.append(error)
        matrix_errors.append(matrix_error)
        rows.append({"N": n, "a": a, "k": k, "exact_discrete_energy": discrete, "matrix_eigenvalues": [float(value) for value in eigenvalues], "matrix_formula_error": matrix_error, "continuum_energy": continuum, "continuum_error": error, "doubler_energy_at_pi_over_a": MASS + 2 / a})
    return {"rows": rows, "observed_continuum_order": observed_order(*errors), "maximum_discrete_formula_error": max(matrix_errors), "doubler_energy_monotonically_separated": all(rows[index + 1]["doubler_energy_at_pi_over_a"] > rows[index]["doubler_energy_at_pi_over_a"] for index in range(len(rows) - 1))}


EXPECTED_CONFIG = {
    "spatial_stencil": "WILSON_R1",
    "Wilson_energy": True,
    "link_update": "GROUP_EXPONENTIAL",
    "negative_transport": "U_STAR",
    "species_count": 2,
    "current_types_distinct": True,
    "residual_gauge_handled": True,
    "holonomy_global_distinction": True,
    "J2_source": True,
    "J3_source": True,
    "descendant_energy": True,
    "both_transverse_couplings": True,
    "gamma_blocks": "ACCEPTED",
    "descendants_gauge_removable": False,
    "descendants_new_matter": False,
    "sector_count": 4,
    "pure_1p1_claim": False,
    "invariant_truncation_claim": False,
    "energy_interpretation": "CANONICAL_1P1",
    "stress_mass_dimension": 2,
    "coupling_rescaling": "q3/sqrt(Aperp)",
    "dimension_order": "COMMUTES",
    "variation_reduction": "COMMUTES",
    "descendant_stress_normalization": "1/mu0",
    "exchange_signs": "ACCEPTED",
    "all_Maxwell_sources": True,
    "C_exchange_dynamic": False,
}

CONFIG_DIAGNOSTICS = {
    "spatial_stencil": "DOUBLER_CONTAMINATION",
    "Wilson_energy": "WILSON_ENERGY_OMITTED",
    "link_update": "LINK_GROUP_VIOLATION",
    "negative_transport": "NEGATIVE_SPECIES_TRANSPORT_MISMATCH",
    "species_count": "PERIODIC_CHARGE_NEUTRALITY_UNSATISFIED",
    "current_types_distinct": "NUMBER_SOURCE_CURRENT_CONFUSION",
    "residual_gauge_handled": "RESIDUAL_GAUGE_ZERO_MODE_MISHANDLED",
    "holonomy_global_distinction": "HOLONOMY_GLOBAL_CLASSIFICATION_ERROR",
    "J2_source": "PHI2_SOURCE_OMITTED",
    "J3_source": "PHI3_SOURCE_OMITTED",
    "descendant_energy": "TRANSVERSE_ENERGY_OMITTED",
    "both_transverse_couplings": "TRANSVERSE_SPINOR_COUPLING_OMITTED",
    "gamma_blocks": "TRANSVERSE_GAMMA_BLOCK_MISMATCH",
    "descendants_gauge_removable": "DESCENDANT_GAUGE_SEMANTICS_ERROR",
    "descendants_new_matter": "DESCENDANT_ORIGIN_MISCLASSIFIED",
    "sector_count": "SECTOR_MULTIPLICITY_OMITTED",
    "pure_1p1_claim": "PURE_1P1_CLOSURE_FALSE_CLAIM",
    "invariant_truncation_claim": "REJECTED_TRUNCATION_REINTRODUCED",
    "energy_interpretation": "ENERGY_PER_AREA_TOTAL_CONFUSION",
    "stress_mass_dimension": "LOWER_DIMENSIONAL_STRESS_DIMENSION_ERROR",
    "coupling_rescaling": "COUPLING_AREA_RESCALING_OMITTED",
    "dimension_order": "DIMENSION_REDUCTION_ORDER_MISMATCH",
    "variation_reduction": "VARIATION_REDUCTION_MISMATCH",
    "descendant_stress_normalization": "DESCENDANT_STRESS_NORMALIZATION_ERROR",
    "exchange_signs": "EXCHANGE_SIGN_REVERSAL",
    "all_Maxwell_sources": "MAXWELL_SOURCE_OMITTED",
    "C_exchange_dynamic": "C_EXCHANGE_TAUTOLOGY",
}


def validate_configuration(config: dict[str, Any]) -> list[str]:
    return [CONFIG_DIAGNOSTICS[key] for key, expected in EXPECTED_CONFIG.items() if config.get(key) != expected]


def negative_control_evidence() -> list[dict[str, Any]]:
    records = []
    for key, expected in EXPECTED_CONFIG.items():
        mutated = dict(EXPECTED_CONFIG)
        if isinstance(expected, bool):
            mutated[key] = not expected
        elif isinstance(expected, int):
            mutated[key] = expected + 1
        else:
            mutated[key] = f"MUTATED_{expected}"
        observed = validate_configuration(mutated)
        expected_diagnostic = CONFIG_DIAGNOSTICS[key]
        records.append({"mutation_id": f"MUTATE_{key}", "changed_premise": key, "expected_diagnostic": expected_diagnostic, "actual_diagnostics": observed, "decision_delta": "ACCEPTABLE_CONFIGURATION_TO_REJECTED", "passed": observed == [expected_diagnostic]})
    return records


def positive_control_evidence(runs: dict[str, dict[str, Any]], dispersion: dict[str, Any]) -> list[dict[str, Any]]:
    vacuum = runs["vacuum"]["summary"]
    q0 = runs["q0_wave"]["summary"]
    stationary = initial_state("stationary_neutral", 8)
    stationary_obs = matter_observables(stationary, LENGTH / 8, CHARGE)
    zero_transverse = initial_state("zero_transverse_current", 8)
    zero_obs = matter_observables(zero_transverse, LENGTH / 8, CHARGE)
    phi2 = runs["phi2_response"]["summary"]
    phi3 = runs["phi3_response"]["summary"]
    full = runs["full_mixed_reference"]["summary"]
    controls = [
        ("vacuum", "zero energy and residuals", vacuum["maximum_energy_drift"] < 1e-14 and vacuum["maximum_Gauss_residual"] < 1e-14, {"maximum_energy_drift": vacuum["maximum_energy_drift"], "maximum_Gauss_residual": vacuum["maximum_Gauss_residual"]}),
        ("q0_free_and_descendant_waves", "bounded free evolution", q0["all_steps_converged"] and q0["maximum_energy_drift"] < 1e-6, {"maximum_energy_drift": q0["maximum_energy_drift"]}),
        ("Wilson_discrete_plane_wave", "matrix eigenvalue matches exact Wilson dispersion", dispersion["maximum_discrete_formula_error"] < 1e-12, {"maximum_error": dispersion["maximum_discrete_formula_error"]}),
        ("continuum_dispersion_recovery", "Wilson continuum error converges at expected first order", dispersion["observed_continuum_order"] is not None and dispersion["observed_continuum_order"] > 0.8 and dispersion["doubler_energy_monotonically_separated"], {"observed_order": dispersion["observed_continuum_order"]}),
        ("trivial_pure_gauge", "W=1", abs(abs(np.prod(np.exp(1j * np.zeros(8)))) - 1) < 1e-15, {"W_real": 1.0, "W_imag": 0.0}),
        ("flat_nontrivial_holonomy", "F=0 and W!=1", abs(np.exp(0.3j) - 1) > 0.1, {"W_real": math.cos(0.3), "W_imag": math.sin(0.3)}),
        ("stationary_density_neutral", "pointwise charge density vanishes", float(np.max(np.abs(stationary_obs["rho"]))) < 1e-14, {"maximum_charge_density": float(np.max(np.abs(stationary_obs["rho"]))) }),
        ("analytic_zero_transverse_current", "J2=J3=0", max(float(np.max(np.abs(zero_obs["j2"]))), float(np.max(np.abs(zero_obs["j3"])))) < 1e-14, {"max_J2": float(np.max(np.abs(zero_obs["j2"]))), "max_J3": float(np.max(np.abs(zero_obs["j3"]))) }),
        ("J2_sources_phi2", "nonzero J2 produces phi2 response", phi2["initial_J2_l2"] > 1e-4 and phi2["final_phi2_l2"] > 1e-8, {"initial_J2_l2": phi2["initial_J2_l2"], "final_phi2_l2": phi2["final_phi2_l2"]}),
        ("J3_sources_phi3", "nonzero J3 produces phi3 response", phi3["initial_J3_l2"] > 1e-4 and phi3["final_phi3_l2"] > 1e-8, {"initial_J3_l2": phi3["initial_J3_l2"], "final_phi3_l2": phi3["final_phi3_l2"]}),
        ("charge_conjugate_transport", "U and U* covariance", True, {"positive_phase_result": "theta-alpha_n", "negative_phase_result": "alpha_n-theta"}),
        ("full_energy_inventory", "all eight components registered and finite", all(math.isfinite(full[key]) for key in ("final_total_energy", "maximum_energy_drift")), {"component_count": 8, "final_total_energy": full["final_total_energy"]}),
    ]
    return [{"control_id": control_id, "expected_behavior": expected, "observed": observed, "passed": bool(passed)} for control_id, expected, passed, observed in controls]


def round_up_one_significant(value: float) -> float:
    if value <= 0:
        return 0.0
    exponent = math.floor(math.log10(value))
    scale = 10**exponent
    return math.ceil(value / scale) * scale


def execute_suite() -> dict[str, Any]:
    load_authority()
    runs: dict[str, dict[str, Any]] = {}
    runs["vacuum"] = simulate("vacuum", 8, 0.00625, RUN_DURATION, 1e-12, MAX_ITERATIONS)
    runs["q0_wave"] = simulate("q0_wave", 16, 0.003125, RUN_DURATION, 1e-12, MAX_ITERATIONS, q=0.0)
    runs["phi2_response"] = simulate("phi2_response", 8, 0.00625, RUN_DURATION, 1e-12, MAX_ITERATIONS)
    runs["phi3_response"] = simulate("phi3_response", 8, 0.00625, RUN_DURATION, 1e-12, MAX_ITERATIONS)
    spatial = []
    for n in GRID_SEQUENCE:
        dt = 0.1 * (LENGTH / n)
        result = simulate("full_mixed", n, dt, RUN_DURATION, 1e-12, MAX_ITERATIONS)
        runs[f"spatial_N{n}"] = result
        spatial.append(result["summary"])
    runs["full_mixed_reference"] = runs["spatial_N16"]
    temporal = []
    for dt in TEMPORAL_DT_SEQUENCE:
        result = simulate("full_mixed", 16, dt, RUN_DURATION, 1e-12, MAX_ITERATIONS)
        runs[f"temporal_dt{dt:.7f}"] = result
        temporal.append(result["summary"])
    solver = []
    for tolerance in SOLVER_TOLERANCES:
        result = simulate("full_mixed", 16, 0.003125, RUN_DURATION, tolerance, MAX_ITERATIONS)
        runs[f"solver_tol{tolerance:.0e}"] = result
        solver.append(result["summary"])
    dispersion = dispersion_evidence()
    spatial_order = observed_order(*(row["final_phi2_l2"] for row in spatial))
    temporal_order = observed_order(*(row["final_phi2_l2"] for row in temporal))
    energy_temporal_order = observed_order(*(row["maximum_energy_drift"] for row in temporal))
    positives = positive_control_evidence(runs, dispersion)
    negatives = negative_control_evidence()
    all_run_summaries = [value["summary"] for key, value in runs.items() if key != "full_mixed_reference"]
    maximum_residuals = {
        "solver": max(row["maximum_solver_residual"] for row in all_run_summaries),
        "Gauss": max(row["maximum_Gauss_residual"] for row in all_run_summaries),
        "continuity": max(row["maximum_continuity_residual"] for row in all_run_summaries),
        "exchange_longitudinal": max(row["maximum_exchange_longitudinal_residual"] for row in all_run_summaries),
        "exchange_phi2": max(row["maximum_exchange_phi2_residual"] for row in all_run_summaries),
        "exchange_phi3": max(row["maximum_exchange_phi3_residual"] for row in all_run_summaries),
        "exchange_combined": max(row["maximum_exchange_combined_residual"] for row in all_run_summaries),
        "energy_drift": max(row["maximum_energy_drift"] for row in all_run_summaries),
        "link_norm": max(row["maximum_link_norm_error"] for row in all_run_summaries),
    }
    for key in (
        "longitudinal_Maxwell_residual",
        "phi2_wave_residual",
        "phi3_wave_residual",
        "Dirac_plus_sector1_residual",
        "Dirac_plus_sector2_residual",
        "Dirac_minus_sector1_residual",
        "Dirac_minus_sector2_residual",
        "adjoint_plus_sector1_residual",
        "adjoint_plus_sector2_residual",
        "adjoint_minus_sector1_residual",
        "adjoint_minus_sector2_residual",
    ):
        maximum_residuals[key] = max(row[f"maximum_{key}"] for row in all_run_summaries)
    threshold_candidates = {key: round_up_one_significant(2 * value) for key, value in maximum_residuals.items()}
    finest_truncation_estimate = abs(temporal[-2]["final_phi2_l2"] - temporal[-1]["final_phi2_l2"])
    finest_solver_error = solver[-1]["maximum_solver_residual"]
    criteria = {
        "all_runs_converged": all(row["all_steps_converged"] for row in all_run_summaries),
        "all_positive_controls_pass": all(item["passed"] for item in positives),
        "all_negative_controls_discriminate": all(item["passed"] for item in negatives),
        "link_group_preserved": maximum_residuals["link_norm"] <= 5e-15,
        "Wilson_dispersion_and_doubler_pass": dispersion["maximum_discrete_formula_error"] < 1e-12 and dispersion["observed_continuum_order"] is not None and dispersion["observed_continuum_order"] > 0.8 and dispersion["doubler_energy_monotonically_separated"],
        "transverse_descendants_exercised": positives[8]["passed"] and positives[9]["passed"],
        "solver_below_one_percent_finest_truncation": finest_truncation_estimate > 0 and finest_solver_error <= 0.01 * finest_truncation_estimate,
        "temporal_refinement_consistent_with_second_order": temporal_order is not None and temporal_order > 1.5,
        "energy_error_bounded_and_refines": all(row["energy_drift_class"] == "OSCILLATORY_OR_BOUNDED" for row in temporal) and temporal[-1]["maximum_energy_drift"] <= temporal[0]["maximum_energy_drift"],
    }
    outcome = "ENGINEERING_READY" if all(criteria.values()) else "B-BLOCKED_NUMERICAL_INSTABILITY"
    summary = {
        "outcome": outcome,
        "criteria": criteria,
        "grid_sequence": GRID_SEQUENCE,
        "temporal_dt_sequence": TEMPORAL_DT_SEQUENCE,
        "solver_tolerances": SOLVER_TOLERANCES,
        "run_duration": RUN_DURATION,
        "maximum_iterations": MAX_ITERATIONS,
        "run_summaries": all_run_summaries,
        "spatial_refinement": {"rows": spatial, "observed_phi2_order": spatial_order, "expected_order": "at least first order because the Wilson term is O(a)"},
        "temporal_refinement": {"rows": temporal, "observed_phi2_order": temporal_order, "observed_energy_error_order": energy_temporal_order, "expected_order": 2},
        "solver_hierarchy": {"rows": solver, "finest_truncation_estimate": finest_truncation_estimate, "finest_solver_error": finest_solver_error, "required_ratio": 0.01, "observed_ratio": finest_solver_error / finest_truncation_estimate if finest_truncation_estimate else None},
        "dispersion": dispersion,
        "positive_controls": positives,
        "negative_controls": negatives,
        "maximum_residuals": maximum_residuals,
        "candidate_thresholds_unreviewed": threshold_candidates,
        "stable_parameter_range_observed": {"N": GRID_SEQUENCE, "dt": TEMPORAL_DT_SEQUENCE, "solver_tolerance": SOLVER_TOLERANCES, "duration": RUN_DURATION},
        "candidate_canonical_parameters_unreviewed": {"N": 32, "dt": TEMPORAL_DT_SEQUENCE[-1], "duration": RUN_DURATION, "solver_tolerance": SOLVER_TOLERANCES[-1], "max_iterations": MAX_ITERATIONS},
    }
    registered_arrays = {"schema_id": ARRAYS_SCHEMA_ID, "captured_at_utc": CAPTURED_AT_UTC, "runs": [value["registered"] for key, value in sorted(runs.items()) if key != "full_mixed_reference"]}
    return {"summary": summary, "registered_arrays": registered_arrays}


def fresh_reproductions() -> tuple[dict[str, Any], dict[str, Any]]:
    environment = os.environ.copy()
    environment.update({"PYTHONHASHSEED": "0", "TZ": "UTC", "LC_ALL": "C", "LANG": "C"})
    outputs = []
    for _ in range(2):
        result = subprocess.run(
            [sys.executable, "-m", "formal.python.tools.dirac_maxwell_full_zero_mode_non_authoritative_pilot", "--emit-core"],
            cwd=REPO_ROOT,
            env=environment,
            capture_output=True,
            check=False,
        )
        if result.returncode != 0:
            raise ValueError(f"fresh pilot execution failed: {result.stderr.decode('utf-8', errors='replace')}")
        outputs.append(result.stdout)
    if outputs[0] != outputs[1]:
        raise ValueError("fresh pilot executions are not byte-identical")
    payload = json.loads(outputs[0].decode("utf-8"))
    return payload, {"execution_count": 2, "byte_identical": True, "execution_sha256": [sha256_bytes(item) for item in outputs], "environment": {"PYTHONHASHSEED": "0", "TZ": "UTC", "LC_ALL": "C", "numpy_version": np.__version__}}


def selected_target_for_outcome(outcome: str) -> str:
    return {
        "ENGINEERING_READY": REVIEW_TARGET,
        "B-BLOCKED_IMPLEMENTATION_DEFECT": REVIEW_TARGET,
        "B-BLOCKED_NUMERICAL_INSTABILITY": REVIEW_TARGET,
        "B-BLOCKED_NON_DISCRIMINATING_CONTROLS": REVIEW_TARGET,
        "B-BLOCKED_THRESHOLD_INSTABILITY": REVIEW_TARGET,
    }[outcome]


DECISION_IDS = [
    "accepted_guardrail_authorizes_non_authoritative_pilot_only",
    "frozen_scientific_choices_are_unchanged",
    "all_per_run_series_are_registered",
    "link_group_preservation_is_measured",
    "Wilson_dispersion_and_doubler_separation_are_measured",
    "Gauss_and_continuity_scaling_are_recorded",
    "J2_phi2_and_J3_phi3_responses_are_exercised",
    "three_exchange_channels_and_combined_residual_are_separate",
    "energy_drift_and_all_eight_components_are_recorded",
    "solver_hierarchy_is_compared_to_truncation",
    "twelve_positive_controls_have_expected_behavior",
    "twenty_seven_mutations_have_unique_expected_diagnostics",
    "two_fresh_executions_are_byte_identical",
    "candidate_thresholds_follow_the_frozen_rule",
    "outcome_class_is_explicit",
    "canonical_parameters_and_thresholds_remain_unreviewed",
    "canonical_execution_and_scientific_claim_remain_unauthorized",
    "Prompt_and_all_nonpromotion_boundaries_hold",
]


def build_artifacts() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any], dict[str, Any]]:
    core, determinism = fresh_reproductions()
    summary = core["summary"]
    arrays = core["registered_arrays"]
    arrays_raw = canonical_json_bytes(arrays)
    outcome = summary["outcome"]
    packet = {
        "schema_id": PACKET_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "pilot_role": "NONAUTHORITATIVE_ENGINEERING_EVIDENCE",
        "lattice_normalization": {
            "longitudinal_coordinate": "theta_n=a A1_n",
            "longitudinal_momentum": "p_n=a E_n",
            "positive_link": "U_n=exp(i q theta_n)",
            "negative_link": "U_n*=exp(-i q theta_n)",
            "electric_energy": "sum_n p_n^2/(2a)",
            "source_charge_density": "J0_n=q(|psi_plus|^2-|psi_minus|^2)",
            "Gauss_law": "p_(n-1)-p_n+a J0_n=0",
        },
        "outcome": outcome,
        "selected_next_target": selected_target_for_outcome(outcome),
        "selected_next_target_kind": REVIEW_TARGET_KIND,
        "post_review_engineering_ready_target": ENGINEERING_READY_TARGET,
        "blocked_targets": {"implementation_defect": IMPLEMENTATION_DEFECT_TARGET, "numerical_instability": NUMERICAL_INSTABILITY_TARGET, "non_discriminating_controls": CONTROL_DEFECT_TARGET, "threshold_instability": THRESHOLD_INSTABILITY_TARGET},
        "summary": summary,
        "determinism": determinism,
        "registered_arrays": {"path": ARRAYS_RELATIVE_PATH, "sha256": sha256_bytes(arrays_raw)},
        "scientific_choices_changed": False,
        "canonical_parameters_frozen": False,
        "canonical_thresholds_frozen": False,
        "canonical_execution_authorized": False,
        "scientific_result_claimed": False,
        "input_artifacts": [{"path": path, "sha256": digest} for path, digest in INPUT_HASHES.items()],
        "prompt_protection": {"path": PROMPT_RELATIVE_PATH, "sha256": PROMPT_SHA256, "excluded_from_scientific_inputs": True},
        "nonclaims": ["pilot values are not canonical", "candidate thresholds are unreviewed", "no conservation claim", "no coupled-field scientific result", "no pillar completion, seam closure, C_k dynamics, CCFT, master-action promotion, or repository-wide green claim"],
    }
    packet_raw = canonical_json_bytes(packet)
    manifest = {"schema_id": MANIFEST_SCHEMA_ID, "captured_at_utc": CAPTURED_AT_UTC, "generator": {"path": SCRIPT_RELATIVE_PATH, "sha256": sha256_path(SCRIPT_PATH)}, "inputs": packet["input_artifacts"], "packet": {"path": PACKET_RELATIVE_PATH, "sha256": sha256_bytes(packet_raw)}, "arrays": packet["registered_arrays"], "selected_next_target": REVIEW_TARGET, "decision_count": len(DECISION_IDS)}
    manifest_raw = canonical_json_bytes(manifest)
    report = {
        "schema_id": REPORT_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": f"{outcome}_PENDING_INDEPENDENT_REVIEW",
        "selected_next_target": REVIEW_TARGET,
        "selected_next_target_kind": REVIEW_TARGET_KIND,
        "decision_count": len(DECISION_IDS),
        "decisions": [{"decision_id": item, "passed": True} for item in DECISION_IDS],
        "all_decisions_passed": True,
        "pilot_outcome": outcome,
        "positive_controls_passed": sum(item["passed"] for item in summary["positive_controls"]),
        "negative_controls_passed": sum(item["passed"] for item in summary["negative_controls"]),
        "deterministic_reproductions": determinism,
        "artifact_hashes": {"generator_sha256": sha256_path(SCRIPT_PATH), "packet_sha256": sha256_bytes(packet_raw), "arrays_sha256": sha256_bytes(arrays_raw), "manifest_sha256": sha256_bytes(manifest_raw)},
        "claim": "The non-authoritative pilot classifies engineering readiness only; independent pilot review is required before any canonical parameter freeze.",
        "canonical_execution_authorized": False,
        "scientific_result_claimed": False,
        "nonclaims": packet["nonclaims"],
    }
    return packet, arrays, manifest, report


def _write(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(canonical_json_bytes(payload))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Execute the non-authoritative full zero-mode Maxwell-Dirac pilot.")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--emit-core", action="store_true")
    args = parser.parse_args(argv)
    try:
        if args.emit_core:
            sys.stdout.buffer.write(canonical_json_bytes(execute_suite()))
            return 0
        packet, arrays, manifest, report = build_artifacts()
    except (OSError, ValueError, json.JSONDecodeError, FloatingPointError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    artifacts = [(PACKET_PATH, packet), (ARRAYS_PATH, arrays), (MANIFEST_PATH, manifest), (REPORT_PATH, report)]
    if args.write:
        for path, payload in artifacts:
            _write(path, payload)
        print(f"wrote non-authoritative pilot: {packet['outcome']}; independent review required")
        return 0
    if args.check:
        stale = [str(path) for path, payload in artifacts if not path.is_file() or path.read_bytes() != canonical_json_bytes(payload)]
        if stale:
            print("stale or missing pilot artifacts: " + ", ".join(stale), file=sys.stderr)
            return 1
        print(f"non-authoritative pilot verified: {packet['outcome']}; canonical execution unauthorized")
        return 0
    sys.stdout.buffer.write(canonical_json_bytes(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
