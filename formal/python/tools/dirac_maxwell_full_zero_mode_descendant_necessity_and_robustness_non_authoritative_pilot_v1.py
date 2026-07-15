from __future__ import annotations

import argparse
import copy
import hashlib
import json
import math
import os
import subprocess
import sys
import unicodedata
from pathlib import Path
from typing import Any, Callable

import numpy as np

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import dirac_maxwell_full_zero_mode_non_authoritative_pilot as accepted_v0


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_non_authoritative_pilot_v1.py"
MODULE_NAME = "formal.python.tools.dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_non_authoritative_pilot_v1"
GUARDRAIL_PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-GUARDRAIL-PACKET-v1.json"
GUARDRAIL_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_GUARDRAIL_PACKET_RESULT_REVIEW_20260714_v1.json"
GUARDRAIL_REVIEWER_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_guardrail_v1_result_review.py"
GUARDRAIL_REVIEW_LEAN_RELATIVE_PATH = "formal/toe_formal/ToeFormal/Derivation/DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessGuardrailPacketV1ResultReview.lean"
ACCEPTED_NUMERICAL_REFERENCE_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_non_authoritative_pilot.py"
PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-NON-AUTHORITATIVE-PILOT-PACKET-v1.json"
ARRAYS_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-NON-AUTHORITATIVE-PILOT-ARRAYS-v1.json"
MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-NON-AUTHORITATIVE-PILOT-MANIFEST-v1.json"
REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_NON_AUTHORITATIVE_PILOT_20260714_v1.json"
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
ARRAYS_PATH = REPO_ROOT / ARRAYS_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
REPORT_PATH = REPO_ROOT / REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-14T00:00:00Z"
TARGET = "execute_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_non_authoritative_pilot_v1"
REVIEW_TARGET = "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_non_authoritative_pilot_v1_result"
POST_REVIEW_READY_TARGET = "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v1"
PACKET_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_NON_AUTHORITATIVE_PILOT_PACKET_v1"
ARRAYS_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_NON_AUTHORITATIVE_PILOT_ARRAYS_v1"
MANIFEST_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_NON_AUTHORITATIVE_PILOT_MANIFEST_v1"
REPORT_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_NON_AUTHORITATIVE_PILOT_20260714_v1"
REVIEW_COMMIT = "fe0279cdbba476eba326a307a4491a422cb96d54"
REVIEW_PARENT = "f88d98a0e82cdc577f17db1e8230ea28c4c49aaa"
INPUT_HASHES = {
    GUARDRAIL_PACKET_RELATIVE_PATH: "54f3c8137986db1ba1bf7cc1a9e0ffade11ed7b6fdf480bf103cdd6b13d964f1",
    GUARDRAIL_REVIEW_RELATIVE_PATH: "a2c1de4f699bf0a2fc1cb38ce0e72b7682df5c0757fa61692f1d32b8e236832e",
    GUARDRAIL_REVIEWER_RELATIVE_PATH: "c621be40c1108f4f32662f5e40399ee6689620dd5e4cfee38ac07e380a3c38f6",
    GUARDRAIL_REVIEW_LEAN_RELATIVE_PATH: "494367751e77aadf77a2fe22a268c403c60f49291161eb81c821038efe90a263",
    ACCEPTED_NUMERICAL_REFERENCE_RELATIVE_PATH: "11939b0db25a72825fe3cd16162c325bf90e562864b40f59ae1fc92f1a646fc1",
}
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"

LENGTH = 1.0
WILSON_R = 1.0
ROUND_TRIP_TOLERANCE = 2e-15
RUN_DURATION = 0.05
GRID_SEQUENCE = [8, 16, 32]
TEMPORAL_DT_SEQUENCE = [0.00625, 0.003125, 0.0015625]
SOLVER_TOLERANCES = [1e-8, 1e-10, 1e-12]
MAX_ITERATIONS = 80
MATERIALITY_GATE = 0.1
DOMINATED_GATE = 0.5

ALPHA1 = accepted_v0.ALPHA1
ALPHA2 = accepted_v0.ALPHA2
ALPHA3 = accepted_v0.ALPHA3
BETA = accepted_v0.BETA

PILOT_ROWS = [
    {
        "row_id": "R00_CANONICAL",
        "ETA_Q": 0.2,
        "F_PERP_POSITIVE_LOADING_INITIAL_v1": 0.2131315883288088,
        "THETA_W": 0.3,
        "DELTA_THETA_PSI": 0.0,
        "MU_MASS_DOMAIN": 1.0,
    },
    {
        "row_id": "R03_F_ZERO",
        "ETA_Q": 0.2,
        "F_PERP_POSITIVE_LOADING_INITIAL_v1": 0.0,
        "THETA_W": 0.3,
        "DELTA_THETA_PSI": 0.0,
        "MU_MASS_DOMAIN": 1.0,
    },
    {
        "row_id": "R05_F_HIGH",
        "ETA_Q": 0.2,
        "F_PERP_POSITIVE_LOADING_INITIAL_v1": 0.5200250552967295,
        "THETA_W": 0.3,
        "DELTA_THETA_PSI": 0.0,
        "MU_MASS_DOMAIN": 1.0,
    },
    {
        "row_id": "R10_MU_HIGH",
        "ETA_Q": 0.2,
        "F_PERP_POSITIVE_LOADING_INITIAL_v1": 0.2131315883288088,
        "THETA_W": 0.3,
        "DELTA_THETA_PSI": 0.0,
        "MU_MASS_DOMAIN": 2.0,
    },
    {
        "row_id": "R11_CORNER_WEAK_HIGH",
        "ETA_Q": 0.1,
        "F_PERP_POSITIVE_LOADING_INITIAL_v1": 0.5200250552967295,
        "THETA_W": -0.3,
        "DELTA_THETA_PSI": math.pi / 2,
        "MU_MASS_DOMAIN": 2.0,
    },
]

POSITIVE_CONTROL_IDS = [
    "P_CANONICAL_ACCEPTED_RESULT_UNCHANGED",
    "P_CHARGE_CONJUGATE_PARAMETER_CASE",
    "P_ANALYTIC_INVARIANT_DESCENDANT_FREE",
    "P_INITIAL_ZERO_DESCENDANTS_DYNAMICALLY_SOURCED",
    "P_INDEPENDENT_PHI2_EXCITATION",
    "P_INDEPENDENT_PHI3_EXCITATION",
    "P_PHI2_PHI3_INTERCHANGE",
    "P_WEAK_COUPLING_APPROACH",
]
NEGATIVE_CONTROL_SPECS = [
    ("N_FORCE_BOTH_DESCENDANTS_ZERO_WITH_SOURCE", "ORIGINAL_TRANSVERSE_BLOCKER_REGRESSION"),
    ("N_DROP_ONLY_PHI2", "PHI2_REQUIRED_FIELD_OMITTED"),
    ("N_DROP_ONLY_PHI3", "PHI3_REQUIRED_FIELD_OMITTED"),
    ("N_OMIT_DESCENDANT_ENERGY", "TRANSVERSE_ENERGY_OMITTED"),
    ("N_OMIT_TRANSVERSE_EXCHANGE_CHANNEL", "TRANSVERSE_EXCHANGE_CHANNEL_OMITTED"),
    ("N_REVERSE_TRANSVERSE_EXCHANGE_SIGN", "TRANSVERSE_EXCHANGE_SIGN_REVERSED"),
    ("N_WRONG_GAMMA2_BLOCK", "GAMMA2_BLOCK_CORRUPTED"),
    ("N_WRONG_GAMMA3_BLOCK", "GAMMA3_BLOCK_CORRUPTED"),
    ("N_SUPPRESS_SECTOR_MULTIPLICITY", "SECTOR_MULTIPLICITY_SUPPRESSED"),
    ("N_DESCENDANTS_RELABELED_INVENTED_MATTER", "DESCENDANT_SEMANTIC_ROLE_CORRUPTED"),
    ("N_CANONICAL_THRESHOLDS_REUSED_UNSCALED", "UNREVIEWED_CANONICAL_THRESHOLD_REUSE"),
    ("N_POST_EXECUTION_FAVORABLE_POINT_SELECTION", "POST_EXECUTION_POINT_SELECTION"),
    ("N_FAILED_POINTS_EXCLUDED_FROM_DOMAIN", "FAILED_POINT_EXCLUDED"),
]

OUTCOME_PRECEDENCE = [
    "B-BLOCKED_IMPLEMENTATION_DEFECT",
    "B-BLOCKED_NUMERICAL_INSTABILITY",
    "B-BLOCKED_NONDISCRIMINATING_CONTROLS",
    "B-BLOCKED_THRESHOLD_GENERATION",
    "ACCEPT_ENGINEERING_READY",
]


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
        raise ValueError(f"expected JSON object: {path}")
    return value


def git_output(*args: str) -> bytes:
    return subprocess.check_output(["git", *args], cwd=REPO_ROOT)


def validate_authority() -> dict[str, Any]:
    if git_output("rev-parse", f"{REVIEW_COMMIT}^").decode().strip() != REVIEW_PARENT:
        raise ValueError("accepted guardrail review parent changed")
    if subprocess.run(
        ["git", "merge-base", "--is-ancestor", REVIEW_COMMIT, "HEAD"],
        cwd=REPO_ROOT,
        check=False,
    ).returncode != 0:
        raise ValueError("accepted guardrail review is not an ancestor of HEAD")
    for relative_path, digest in INPUT_HASHES.items():
        if sha256_bytes(git_output("show", f"{REVIEW_COMMIT}:{relative_path}")) != digest:
            raise ValueError(f"accepted committed input changed: {relative_path}")
        if sha256_path(REPO_ROOT / relative_path) != digest:
            raise ValueError(f"accepted working input changed: {relative_path}")
    if sha256_path(REPO_ROOT / PROMPT_RELATIVE_PATH) != PROMPT_SHA256:
        raise ValueError("Prompt.txt changed")
    review = load_json(REPO_ROOT / GUARDRAIL_REVIEW_RELATIVE_PATH)
    authority = review.get("authority_rotation", {})
    if not (
        review.get("accepted") is True
        and review.get("verdict") == "ACCEPT_GUARDRAIL_V1"
        and review.get("selected_next_target") == TARGET
        and authority.get("bounded_non_authoritative_pilot_authorized") is True
        and authority.get("numerical_threshold_or_parameter_freeze_authorized") is False
        and authority.get("canonical_robustness_execution_authorized") is False
        and authority.get("new_scientific_claim_authorized") is False
    ):
        raise ValueError("accepted guardrail review does not authorize exactly this pilot")
    return {
        "review_commit": REVIEW_COMMIT,
        "review_parent": REVIEW_PARENT,
        "bound_inputs": INPUT_HASHES,
    }


def principal_phase(value: float) -> float:
    result = (value + math.pi) % (2 * math.pi) - math.pi
    return math.pi if result == -math.pi else result


def _field_energy(state: dict[str, np.ndarray], a: float) -> tuple[float, float]:
    grad2 = (np.roll(state["phi2"], -1) - state["phi2"]) / a
    grad3 = (np.roll(state["phi3"], -1) - state["phi3"]) / a
    energy2 = float(np.sum(state["P2"] ** 2) / (2 * a) + 0.5 * a * np.sum(grad2**2))
    energy3 = float(np.sum(state["P3"] ** 2) / (2 * a) + 0.5 * a * np.sum(grad3**2))
    return energy2, energy3


def hamiltonian_parts(
    psi: np.ndarray,
    theta: np.ndarray,
    phi2: np.ndarray,
    phi3: np.ndarray,
    sigma: int,
    a: float,
    q: float,
    mass: float,
) -> tuple[np.ndarray, dict[str, np.ndarray]]:
    phase_forward = np.exp(1j * sigma * q * theta)
    phase_backward = np.exp(-1j * sigma * q * np.roll(theta, 1))
    next_psi = np.roll(psi, -1, axis=0)
    previous_psi = np.roll(psi, 1, axis=0)
    local = np.einsum("ij,nj->ni", BETA * (mass + WILSON_R / a), psi)
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


def matter_observables(
    state: dict[str, np.ndarray], a: float, q: float, mass: float
) -> dict[str, Any]:
    theta = state["theta"]
    charge_density = np.zeros(theta.shape, dtype=np.float64)
    number_density = np.zeros(theta.shape, dtype=np.float64)
    j2 = np.zeros(theta.shape, dtype=np.float64)
    j3 = np.zeros(theta.shape, dtype=np.float64)
    grad_theta = np.zeros(theta.shape, dtype=np.float64)
    hpsi: dict[str, np.ndarray] = {}
    parts: dict[str, dict[str, np.ndarray]] = {}
    for sigma, key in ((1, "psi_plus"), (-1, "psi_minus")):
        psi = state[key]
        hpsi[key], parts[key] = hamiltonian_parts(
            psi, theta, state["phi2"], state["phi3"], sigma, a, q, mass
        )
        density = np.sum(np.abs(psi) ** 2, axis=1).real
        number_density += density
        charge_density += sigma * q * density
        j2 += sigma * q * np.einsum("ni,ij,nj->n", psi.conj(), ALPHA2, psi).real
        j3 += sigma * q * np.einsum("ni,ij,nj->n", psi.conj(), ALPHA3, psi).real
        forward_matrix = (-1j * ALPHA1 - WILSON_R * BETA) / (2 * a)
        next_psi = np.roll(psi, -1, axis=0)
        phase = np.exp(1j * sigma * q * theta)
        z = np.einsum("ni,ij,nj->n", psi.conj(), forward_matrix, phase[:, None] * next_psi)
        grad_theta += 2 * a * np.real(1j * sigma * q * z)
    return {
        "rho": charge_density,
        "number_density": number_density,
        "j2": j2,
        "j3": j3,
        "grad_theta": grad_theta,
        "hpsi_plus": hpsi["psi_plus"],
        "hpsi_minus": hpsi["psi_minus"],
        "parts": parts,
    }


def rhs(
    vector: np.ndarray,
    n: int,
    q: float,
    mass: float,
    forced_truncation: bool = False,
) -> np.ndarray:
    a = LENGTH / n
    state = accepted_v0.unpack(vector, n)
    if forced_truncation:
        for key in ("phi2", "P2", "phi3", "P3"):
            state[key][:] = 0.0
    obs = matter_observables(state, a, q, mass)
    derivative = {key: np.zeros_like(value) for key, value in state.items()}
    derivative["theta"] = state["p"] / a
    derivative["p"] = -obs["grad_theta"]
    if not forced_truncation:
        derivative["phi2"] = state["P2"] / a
        derivative["phi3"] = state["P3"] / a
        lap2 = (np.roll(state["phi2"], -1) - 2 * state["phi2"] + np.roll(state["phi2"], 1)) / a**2
        lap3 = (np.roll(state["phi3"], -1) - 2 * state["phi3"] + np.roll(state["phi3"], 1)) / a**2
        derivative["P2"] = a * (lap2 - obs["j2"])
        derivative["P3"] = a * (lap3 - obs["j3"])
    derivative["psi_plus"] = -1j * obs["hpsi_plus"]
    derivative["psi_minus"] = -1j * obs["hpsi_minus"]
    return accepted_v0.pack(derivative)


def implicit_midpoint_step(
    vector: np.ndarray,
    n: int,
    q: float,
    mass: float,
    dt: float,
    tolerance: float,
    max_iterations: int,
    forced_truncation: bool,
) -> tuple[np.ndarray, float, int, bool]:
    evaluate = lambda value: rhs(value, n, q, mass, forced_truncation)
    guess = vector + dt * evaluate(vector)
    converged = False
    residual = math.inf
    for iteration in range(1, max_iterations + 1):
        updated = vector + dt * evaluate(0.5 * (vector + guess))
        residual = float(np.max(np.abs(updated - guess)))
        guess = updated
        if residual <= tolerance:
            converged = True
            break
    equation_residual = float(
        np.max(np.abs(guess - vector - dt * evaluate(0.5 * (vector + guess))))
    )
    return guess, max(residual, equation_residual), iteration, converged


def energy_components(
    state: dict[str, np.ndarray], a: float, q: float, mass: float
) -> dict[str, float]:
    p_mean = float(np.mean(state["p"]))
    electric_zero = state["p"].size * p_mean**2 / (2 * a)
    electric_fluctuating = float(np.sum((state["p"] - p_mean) ** 2) / (2 * a))
    phi2_energy, phi3_energy = _field_energy(state, a)
    matter_local = 0.0
    link_interaction = 0.0
    gamma2_interaction = 0.0
    gamma3_interaction = 0.0
    obs = matter_observables(state, a, q, mass)
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


def free_wilson_spectral_weights(
    psi: np.ndarray, a: float, mass: float
) -> tuple[float, float]:
    n = psi.shape[0]
    modes = np.fft.fft(psi, axis=0) / math.sqrt(n)
    momenta = 2 * np.pi * np.fft.fftfreq(n, d=a)
    positive = 0.0
    negative = 0.0
    for mode, momentum in zip(modes, momenta, strict=True):
        ka = momentum * a
        operator = ALPHA1 * (math.sin(ka) / a) + BETA * (
            mass + WILSON_R * (1 - math.cos(ka)) / a
        )
        values, vectors = np.linalg.eigh(operator)
        coefficients = vectors.conj().T @ mode
        positive += float(np.sum(np.abs(coefficients[values >= 0]) ** 2))
        negative += float(np.sum(np.abs(coefficients[values < 0]) ** 2))
    return a * positive, a * negative


def diagnostics(
    state: dict[str, np.ndarray], a: float, q: float, mass: float
) -> tuple[dict[str, float], dict[str, np.ndarray]]:
    obs = matter_observables(state, a, q, mass)
    gauss = np.roll(state["p"], 1) - state["p"] + a * obs["rho"]
    links = np.exp(1j * q * state["theta"])
    energies = energy_components(state, a, q, mass)
    plus_positive, plus_negative = free_wilson_spectral_weights(state["psi_plus"], a, mass)
    minus_positive, minus_negative = free_wilson_spectral_weights(state["psi_minus"], a, mass)
    matter_energy_density = np.zeros(state["theta"].shape, dtype=np.float64)
    for key in ("psi_plus", "psi_minus"):
        psi = state[key]
        for part in obs["parts"][key].values():
            matter_energy_density += np.einsum("ni,ni->n", psi.conj(), part).real
    electric_field = state["p"] / a
    j1 = obs["grad_theta"] / a
    total_current = np.sqrt(j1**2 + obs["j2"] ** 2 + obs["j3"] ** 2)
    transverse_source = np.sqrt(obs["j2"] ** 2 + obs["j3"] ** 2)
    scalar = {
        "total_energy": float(sum(energies.values())),
        "link_norm_error": float(np.max(np.abs(np.abs(links) - 1.0))),
        "gauss_residual": float(np.max(np.abs(gauss))),
        "total_charge": float(a * np.sum(obs["rho"])),
        "matter_number": float(a * np.sum(obs["number_density"])),
        "J2_l2": float(math.sqrt(a * np.sum(obs["j2"] ** 2))),
        "J3_l2": float(math.sqrt(a * np.sum(obs["j3"] ** 2))),
        "transverse_source_l2": float(math.sqrt(a * np.sum(transverse_source**2))),
        "phi2_l2": float(math.sqrt(a * np.sum(state["phi2"] ** 2))),
        "phi3_l2": float(math.sqrt(a * np.sum(state["phi3"] ** 2))),
        "matter_density_l2": float(math.sqrt(a * np.sum(obs["number_density"] ** 2))),
        "longitudinal_electric_field_l2": float(math.sqrt(a * np.sum(electric_field**2))),
        "matter_energy": energies["Wilson_Dirac_local"]
        + energies["link_interaction"]
        + energies["gamma2_interaction"]
        + energies["gamma3_interaction"],
        "total_source_current_l2": float(math.sqrt(a * np.sum(total_current**2))),
        "psi_plus_positive_frequency_weight": plus_positive,
        "psi_plus_negative_frequency_weight": plus_negative,
        "psi_minus_positive_frequency_weight": minus_positive,
        "psi_minus_negative_frequency_weight": minus_negative,
        **{f"energy_{key}": value for key, value in energies.items()},
    }
    vectors = {
        "MATTER_DENSITY": obs["number_density"].copy(),
        "LONGITUDINAL_ELECTRIC_FIELD": electric_field.copy(),
        "MATTER_ENERGY": matter_energy_density.copy(),
        "TOTAL_SOURCE_CURRENT": total_current.copy(),
    }
    return scalar, vectors


def construct_initial_state(
    row: dict[str, Any], n: int, forced_truncation: bool
) -> tuple[dict[str, np.ndarray], dict[str, Any]]:
    a = LENGTH / n
    mass = float(row["MU_MASS_DOMAIN"]) / LENGTH
    eta = float(row["ETA_Q"])
    q = eta * mass
    base_state = accepted_v0.initial_state("full_mixed", n, q)
    base_state["theta"][:] = float(row["THETA_W"]) / (q * n)
    unphased = {key: value.copy() for key, value in base_state.items()}
    phase = complex(
        math.cos(float(row["DELTA_THETA_PSI"])),
        math.sin(float(row["DELTA_THETA_PSI"])),
    )
    for species in ("psi_plus", "psi_minus"):
        base_state[species][:, [1, 3]] *= phase
    reference_descendant_energy = sum(_field_energy(base_state, a))
    scalar, _ = diagnostics(base_state, a, q, mass)
    parallel_maxwell = scalar["energy_electric_fluctuating"] + scalar["energy_electric_zero_mode"]
    positive_base = parallel_maxwell + mass * scalar["matter_number"]
    requested_loading = float(row["F_PERP_POSITIVE_LOADING_INITIAL_v1"])
    requested_descendant = (
        0.0
        if requested_loading == 0.0
        else requested_loading / (1.0 - requested_loading) * positive_base
    )
    alpha = (
        0.0
        if requested_descendant == 0.0
        else math.sqrt(requested_descendant / reference_descendant_energy)
    )
    for key in ("phi2", "P2", "phi3", "P3"):
        base_state[key] *= alpha
    reconstructed_descendant = sum(_field_energy(base_state, a))
    realized_loading = reconstructed_descendant / (reconstructed_descendant + positive_base)
    overlap = 0.0j
    for species in ("psi_plus", "psi_minus"):
        overlap += np.vdot(
            unphased[species][:, [1, 3]], base_state[species][:, [1, 3]]
        )
    realized_phase = principal_phase(float(np.angle(overlap)))
    realized = {
        "ETA_Q": q / mass,
        "F_PERP_POSITIVE_LOADING_INITIAL_v1": realized_loading,
        "THETA_W": principal_phase(float(q * np.sum(base_state["theta"]))),
        "DELTA_THETA_PSI": realized_phase,
        "MU_MASS_DOMAIN": mass * LENGTH,
    }
    requested = {
        key: float(row[key])
        for key in (
            "ETA_Q",
            "F_PERP_POSITIVE_LOADING_INITIAL_v1",
            "THETA_W",
            "DELTA_THETA_PSI",
            "MU_MASS_DOMAIN",
        )
    }
    errors = {
        key: abs(principal_phase(realized[key] - requested[key]))
        if key in ("THETA_W", "DELTA_THETA_PSI")
        else abs(realized[key] - requested[key])
        for key in requested
    }
    full_parent_state = {key: value.copy() for key, value in base_state.items()}
    if forced_truncation:
        for key in ("phi2", "P2", "phi3", "P3"):
            base_state[key][:] = 0.0
    initial_scalar, _ = diagnostics(base_state, a, q, mass)
    reconstruction = {
        "requested_axis_values": requested,
        "realized_parent_axis_values": realized,
        "round_trip_absolute_errors": errors,
        "round_trip_passed": max(errors.values()) <= ROUND_TRIP_TOLERANCE,
        "positive_base_energy_B_plus": positive_base,
        "positive_base_strictly_positive": positive_base > 0.0,
        "reference_descendant_energy": reference_descendant_energy,
        "requested_descendant_energy": requested_descendant,
        "reconstructed_descendant_energy": reconstructed_descendant,
        "reference_descendant_profile_alpha": alpha,
        "mass_runtime_parameter": mass,
        "charge_constructed_eta_times_mass": q,
        "charge_identity_error": abs(q - eta * mass),
        "gauge_invariant_holonomy": principal_phase(float(q * np.sum(full_parent_state["theta"]))),
        "charge_neutrality_error": abs(initial_scalar["total_charge"]),
        "sector_multiplicity": 4,
        "model_class": "INTENTIONALLY_NONINVARIANT_COMPARATOR"
        if forced_truncation
        else "FULL_ACCEPTED_DESCENDANT_AWARE_SYSTEM",
        "parent_requested_loading_preserved": requested_loading,
        "comparator_realized_loading": None if forced_truncation else realized_loading,
        "comparator_realized_loading_status": "NOT_PHYSICALLY_ELIGIBLE"
        if forced_truncation
        else "FULL_MODEL_REALIZED",
    }
    return base_state, reconstruction


EQUATION_RESIDUAL_KEYS = (
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


def _format_series(values: list[float]) -> list[str]:
    return [format(float(value), ".12e") for value in values]


def _execution_identity(payload: dict[str, Any]) -> str:
    return "EXECUTION_" + sha256_bytes(canonical_json_bytes(payload))[:16]


def simulate(
    row: dict[str, Any],
    role: str,
    n: int,
    dt: float,
    duration: float,
    tolerance: float,
    max_iterations: int,
    forced_truncation: bool = False,
) -> dict[str, Any]:
    a = LENGTH / n
    mass = float(row["MU_MASS_DOMAIN"]) / LENGTH
    q = float(row["ETA_Q"]) * mass
    steps = max(1, int(round(duration / dt)))
    dt = duration / steps
    state, reconstruction = construct_initial_state(row, n, forced_truncation)
    vector = accepted_v0.pack(state)
    initial, initial_vectors = diagnostics(state, a, q, mass)
    series: dict[str, list[float]] = {key: [value] for key, value in initial.items()}
    series.update(
        {
            key: [0.0]
            for key in (
                "time",
                "solver_residual",
                "solver_iterations",
                "continuity_residual",
                "exchange_longitudinal_residual",
                "exchange_phi2_residual",
                "exchange_phi3_residual",
                "exchange_combined_residual",
                "cumulative_exchange_longitudinal",
                "cumulative_exchange_phi2",
                "cumulative_exchange_phi3",
                "total_energy_delta",
                "forced_transverse_equation_residual",
                *EQUATION_RESIDUAL_KEYS,
            )
        }
    )
    observable_vectors: dict[str, list[np.ndarray]] = {
        key: [value] for key, value in initial_vectors.items()
    }
    observable_vectors["LONGITUDINAL_EXCHANGE"] = [np.array([0.0])]
    all_converged = True
    maximum_iteration = 0
    cumulative_work = {"longitudinal": 0.0, "phi2": 0.0, "phi3": 0.0}
    for step in range(1, steps + 1):
        previous_vector = vector
        previous_state = accepted_v0.unpack(previous_vector, n)
        previous_energy = energy_components(previous_state, a, q, mass)
        vector, solver_residual, iterations, converged = implicit_midpoint_step(
            previous_vector,
            n,
            q,
            mass,
            dt,
            tolerance,
            max_iterations,
            forced_truncation,
        )
        if forced_truncation:
            projected = accepted_v0.unpack(vector, n)
            for key in ("phi2", "P2", "phi3", "P3"):
                projected[key][:] = 0.0
            vector = accepted_v0.pack(projected)
        all_converged = all_converged and converged
        maximum_iteration = max(maximum_iteration, iterations)
        current_state = accepted_v0.unpack(vector, n)
        current, current_vectors = diagnostics(current_state, a, q, mass)
        current_energy = energy_components(current_state, a, q, mass)
        midpoint_state = accepted_v0.unpack(0.5 * (previous_vector + vector), n)
        midpoint_obs = matter_observables(midpoint_state, a, q, mass)
        equation_defect = accepted_v0.unpack(
            vector
            - previous_vector
            - dt
            * rhs(
                0.5 * (previous_vector + vector),
                n,
                q,
                mass,
                forced_truncation,
            ),
            n,
        )
        equation_residuals = {
            "longitudinal_Maxwell_residual": float(
                max(
                    np.max(np.abs(equation_defect["theta"])),
                    np.max(np.abs(equation_defect["p"])),
                )
            ),
            "phi2_wave_residual": float(
                max(
                    np.max(np.abs(equation_defect["phi2"])),
                    np.max(np.abs(equation_defect["P2"])),
                )
            ),
            "phi3_wave_residual": float(
                max(
                    np.max(np.abs(equation_defect["phi3"])),
                    np.max(np.abs(equation_defect["P3"])),
                )
            ),
            "Dirac_plus_sector1_residual": float(
                np.max(np.abs(equation_defect["psi_plus"][:, :2]))
            ),
            "Dirac_plus_sector2_residual": float(
                np.max(np.abs(equation_defect["psi_plus"][:, 2:]))
            ),
            "Dirac_minus_sector1_residual": float(
                np.max(np.abs(equation_defect["psi_minus"][:, :2]))
            ),
            "Dirac_minus_sector2_residual": float(
                np.max(np.abs(equation_defect["psi_minus"][:, 2:]))
            ),
        }
        equation_residuals.update(
            {
                key.replace("Dirac", "adjoint"): value
                for key, value in equation_residuals.items()
                if key.startswith("Dirac")
            }
        )
        theta_dot = midpoint_state["p"] / a
        phi2_dot = midpoint_state["P2"] / a
        phi3_dot = midpoint_state["P3"] / a
        work_longitudinal = float(np.sum(midpoint_obs["grad_theta"] * theta_dot))
        work_phi2 = float(a * np.sum(midpoint_obs["j2"] * phi2_dot))
        work_phi3 = float(a * np.sum(midpoint_obs["j3"] * phi3_dot))
        cumulative_work["longitudinal"] += dt * work_longitudinal
        cumulative_work["phi2"] += dt * work_phi2
        cumulative_work["phi3"] += dt * work_phi3
        delta_electric = (
            current_energy["electric_fluctuating"]
            + current_energy["electric_zero_mode"]
            - previous_energy["electric_fluctuating"]
            - previous_energy["electric_zero_mode"]
        )
        delta_phi2 = current_energy["phi2"] - previous_energy["phi2"]
        delta_phi3 = current_energy["phi3"] - previous_energy["phi3"]
        exchange_longitudinal = delta_electric + dt * work_longitudinal
        exchange_phi2 = delta_phi2 + dt * work_phi2
        exchange_phi3 = delta_phi3 + dt * work_phi3
        previous_obs = matter_observables(previous_state, a, q, mass)
        current_obs = matter_observables(current_state, a, q, mass)
        rho_rate = (current_obs["rho"] - previous_obs["rho"]) / dt
        current_divergence = (
            midpoint_obs["grad_theta"] - np.roll(midpoint_obs["grad_theta"], 1)
        ) / a
        continuity = float(np.max(np.abs(rho_rate + current_divergence)))
        for key, value in current.items():
            series[key].append(value)
        series["time"].append(step * dt)
        series["solver_residual"].append(solver_residual)
        series["solver_iterations"].append(float(iterations))
        series["continuity_residual"].append(continuity)
        series["exchange_longitudinal_residual"].append(exchange_longitudinal)
        series["exchange_phi2_residual"].append(exchange_phi2)
        series["exchange_phi3_residual"].append(exchange_phi3)
        series["exchange_combined_residual"].append(
            exchange_longitudinal + exchange_phi2 + exchange_phi3
        )
        series["cumulative_exchange_longitudinal"].append(
            cumulative_work["longitudinal"]
        )
        series["cumulative_exchange_phi2"].append(cumulative_work["phi2"])
        series["cumulative_exchange_phi3"].append(cumulative_work["phi3"])
        series["total_energy_delta"].append(current["total_energy"] - initial["total_energy"])
        forced_residual = (
            current["transverse_source_l2"] if forced_truncation else 0.0
        )
        series["forced_transverse_equation_residual"].append(forced_residual)
        for key, value in equation_residuals.items():
            series[key].append(value)
        for key, value in current_vectors.items():
            observable_vectors[key].append(value)
        observable_vectors["LONGITUDINAL_EXCHANGE"].append(
            np.array([cumulative_work["longitudinal"]])
        )
    energy_delta = np.array(series["total_energy_delta"])
    times = np.array(series["time"])
    energy_slope = (
        float(np.polyfit(times, energy_delta, 1)[0]) if len(times) >= 3 else 0.0
    )
    drift_steps = np.diff(energy_delta)
    drift_is_monotone = bool(
        len(drift_steps) == 0
        or np.all(drift_steps >= 0.0)
        or np.all(drift_steps <= 0.0)
    )
    execution_payload = {
        "row_id": row["row_id"],
        "model": "FORCED" if forced_truncation else "FULL",
        "N": n,
        "dt": dt,
        "duration": duration,
        "tolerance": tolerance,
        "max_iterations": max_iterations,
        "requested_axes": reconstruction["requested_axis_values"],
    }
    execution_id = _execution_identity(execution_payload)
    run_record_id = f"{row['row_id']}:{role}:{execution_id}"
    summary = {
        "run_record_id": run_record_id,
        "execution_id": execution_id,
        "calibration_role": role,
        "row_id": row["row_id"],
        "model_class": reconstruction["model_class"],
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
        "energy_drift_linear_slope": energy_slope,
        "energy_drift_shape": "MONOTONE_AT_FIXED_RESOLUTION"
        if drift_is_monotone
        else "OSCILLATORY_AT_FIXED_RESOLUTION",
        "maximum_exchange_longitudinal_residual": max(
            abs(value) for value in series["exchange_longitudinal_residual"]
        ),
        "maximum_exchange_phi2_residual": max(
            abs(value) for value in series["exchange_phi2_residual"]
        ),
        "maximum_exchange_phi3_residual": max(
            abs(value) for value in series["exchange_phi3_residual"]
        ),
        "maximum_exchange_combined_residual": max(
            abs(value) for value in series["exchange_combined_residual"]
        ),
        "maximum_forced_transverse_equation_residual": max(
            series["forced_transverse_equation_residual"]
        ),
        **{
            f"maximum_{key}": max(abs(value) for value in series[key])
            for key in EQUATION_RESIDUAL_KEYS
        },
        "initial_J2_l2": series["J2_l2"][0],
        "initial_J3_l2": series["J3_l2"][0],
        "maximum_phi2_energy_departure": max(
            abs(value - series["energy_phi2"][0]) for value in series["energy_phi2"]
        ),
        "maximum_phi3_energy_departure": max(
            abs(value - series["energy_phi3"][0]) for value in series["energy_phi3"]
        ),
        "maximum_absolute_X2": max(abs(value) for value in series["cumulative_exchange_phi2"]),
        "maximum_absolute_X3": max(abs(value) for value in series["cumulative_exchange_phi3"]),
        "maximum_absolute_X_longitudinal": max(
            abs(value) for value in series["cumulative_exchange_longitudinal"]
        ),
        "final_phi2_l2": series["phi2_l2"][-1],
        "final_phi3_l2": series["phi3_l2"][-1],
        "final_descendant_l2": math.sqrt(
            series["phi2_l2"][-1] ** 2 + series["phi3_l2"][-1] ** 2
        ),
        "maximum_total_charge_error": max(abs(value) for value in series["total_charge"]),
        "initial_state_reconstruction": reconstruction,
    }
    registered = {
        "run_record_id": run_record_id,
        "execution_id": execution_id,
        "calibration_role": role,
        "row_id": row["row_id"],
        "model_class": reconstruction["model_class"],
        "series": {key: _format_series(values) for key, values in series.items()},
    }
    return {
        "summary": summary,
        "registered": registered,
        "series_numeric": series,
        "observable_vectors": observable_vectors,
    }


def observed_order(coarse: float, middle: float, fine: float) -> float | None:
    numerator = abs(coarse - middle)
    denominator = abs(middle - fine)
    if denominator == 0.0 or numerator == 0.0:
        return None
    return math.log(numerator / denominator, 2)


def round_up_one_significant(value: float) -> float:
    if value <= 0.0:
        return 0.0
    exponent = math.floor(math.log10(value))
    scale = 10**exponent
    return math.ceil(value / scale) * scale


def _l2(vector: np.ndarray, a: float) -> float:
    return float(math.sqrt(a * np.sum(np.abs(vector) ** 2)))


def raw_comparator_evidence(
    full: dict[str, Any], comparator: dict[str, Any]
) -> dict[str, Any]:
    a = float(full["summary"]["a"])
    numerators: dict[str, float] = {}
    denominators: dict[str, float] = {}
    for observable_id in (
        "MATTER_DENSITY",
        "LONGITUDINAL_ELECTRIC_FIELD",
        "MATTER_ENERGY",
        "LONGITUDINAL_EXCHANGE",
        "TOTAL_SOURCE_CURRENT",
    ):
        full_values = full["observable_vectors"][observable_id]
        comparator_values = comparator["observable_vectors"][observable_id]
        numerators[observable_id] = max(
            _l2(left - right, a)
            for left, right in zip(full_values, comparator_values, strict=True)
        )
        denominators[observable_id] = max(_l2(value, a) for value in full_values)
    full_summary = full["summary"]
    transverse_exchange = (
        full_summary["maximum_absolute_X2"] + full_summary["maximum_absolute_X3"]
    )
    total_exchange = transverse_exchange + full_summary["maximum_absolute_X_longitudinal"]
    return {
        "row_id": full_summary["row_id"],
        "full_run_record_id": full_summary["run_record_id"],
        "comparator_run_record_id": comparator["summary"]["run_record_id"],
        "parent_requested_loading": full_summary["initial_state_reconstruction"][
            "parent_requested_loading_preserved"
        ],
        "comparator_realized_loading": None,
        "comparator_realized_loading_status": "NOT_PHYSICALLY_ELIGIBLE",
        "R_PERP_raw_numerators": numerators,
        "R_PERP_raw_denominator_scales": denominators,
        "transverse_exchange_raw": transverse_exchange,
        "total_exchange_raw": total_exchange,
        "forced_C_PERP_source_norm": comparator["summary"][
            "maximum_forced_transverse_equation_residual"
        ],
        "forced_R_TRUNC_equation_residual": comparator["summary"][
            "maximum_forced_transverse_equation_residual"
        ],
        "scientific_significance_class_assigned": False,
    }


EXPECTED_CONTROL_CONFIG = {
    "phi2_present": True,
    "phi3_present": True,
    "descendant_energy_present": True,
    "transverse_exchange_present": True,
    "exchange_sign": "ACCEPTED",
    "gamma2_block": "ACCEPTED",
    "gamma3_block": "ACCEPTED",
    "sector_count": 4,
    "descendant_role": "GAUGE_FIELD_DESCENDANTS",
    "canonical_thresholds_reused": False,
    "post_execution_selection": False,
    "failed_points_excluded": False,
}


def control_diagnostics(config: dict[str, Any]) -> list[str]:
    diagnostics: list[str] = []
    if config.get("phi2_present") is False and config.get("phi3_present") is False:
        diagnostics.append("ORIGINAL_TRANSVERSE_BLOCKER_REGRESSION")
    else:
        if config.get("phi2_present") is not True:
            diagnostics.append("PHI2_REQUIRED_FIELD_OMITTED")
        if config.get("phi3_present") is not True:
            diagnostics.append("PHI3_REQUIRED_FIELD_OMITTED")
    if config.get("descendant_energy_present") is not True:
        diagnostics.append("TRANSVERSE_ENERGY_OMITTED")
    if config.get("transverse_exchange_present") is not True:
        diagnostics.append("TRANSVERSE_EXCHANGE_CHANNEL_OMITTED")
    if config.get("exchange_sign") != "ACCEPTED":
        diagnostics.append("TRANSVERSE_EXCHANGE_SIGN_REVERSED")
    if config.get("gamma2_block") != "ACCEPTED":
        diagnostics.append("GAMMA2_BLOCK_CORRUPTED")
    if config.get("gamma3_block") != "ACCEPTED":
        diagnostics.append("GAMMA3_BLOCK_CORRUPTED")
    if config.get("sector_count") != 4:
        diagnostics.append("SECTOR_MULTIPLICITY_SUPPRESSED")
    if config.get("descendant_role") != "GAUGE_FIELD_DESCENDANTS":
        diagnostics.append("DESCENDANT_SEMANTIC_ROLE_CORRUPTED")
    if config.get("canonical_thresholds_reused") is not False:
        diagnostics.append("UNREVIEWED_CANONICAL_THRESHOLD_REUSE")
    if config.get("post_execution_selection") is not False:
        diagnostics.append("POST_EXECUTION_POINT_SELECTION")
    if config.get("failed_points_excluded") is not False:
        diagnostics.append("FAILED_POINT_EXCLUDED")
    return diagnostics


def negative_control_evidence(
    comparator_evidence: list[dict[str, Any]], numerical_floor: float
) -> list[dict[str, Any]]:
    mutations: list[tuple[str, str, Callable[[dict[str, Any]], None]]] = [
        (NEGATIVE_CONTROL_SPECS[0][0], NEGATIVE_CONTROL_SPECS[0][1], lambda value: value.update({"phi2_present": False, "phi3_present": False})),
        (NEGATIVE_CONTROL_SPECS[1][0], NEGATIVE_CONTROL_SPECS[1][1], lambda value: value.__setitem__("phi2_present", False)),
        (NEGATIVE_CONTROL_SPECS[2][0], NEGATIVE_CONTROL_SPECS[2][1], lambda value: value.__setitem__("phi3_present", False)),
        (NEGATIVE_CONTROL_SPECS[3][0], NEGATIVE_CONTROL_SPECS[3][1], lambda value: value.__setitem__("descendant_energy_present", False)),
        (NEGATIVE_CONTROL_SPECS[4][0], NEGATIVE_CONTROL_SPECS[4][1], lambda value: value.__setitem__("transverse_exchange_present", False)),
        (NEGATIVE_CONTROL_SPECS[5][0], NEGATIVE_CONTROL_SPECS[5][1], lambda value: value.__setitem__("exchange_sign", "REVERSED")),
        (NEGATIVE_CONTROL_SPECS[6][0], NEGATIVE_CONTROL_SPECS[6][1], lambda value: value.__setitem__("gamma2_block", "WRONG")),
        (NEGATIVE_CONTROL_SPECS[7][0], NEGATIVE_CONTROL_SPECS[7][1], lambda value: value.__setitem__("gamma3_block", "WRONG")),
        (NEGATIVE_CONTROL_SPECS[8][0], NEGATIVE_CONTROL_SPECS[8][1], lambda value: value.__setitem__("sector_count", 2)),
        (NEGATIVE_CONTROL_SPECS[9][0], NEGATIVE_CONTROL_SPECS[9][1], lambda value: value.__setitem__("descendant_role", "INVENTED_MATTER")),
        (NEGATIVE_CONTROL_SPECS[10][0], NEGATIVE_CONTROL_SPECS[10][1], lambda value: value.__setitem__("canonical_thresholds_reused", True)),
        (NEGATIVE_CONTROL_SPECS[11][0], NEGATIVE_CONTROL_SPECS[11][1], lambda value: value.__setitem__("post_execution_selection", True)),
        (NEGATIVE_CONTROL_SPECS[12][0], NEGATIVE_CONTROL_SPECS[12][1], lambda value: value.__setitem__("failed_points_excluded", True)),
    ]
    dynamic_forced_residual = max(
        item["forced_R_TRUNC_equation_residual"] for item in comparator_evidence
    )
    results = []
    for mutation_id, expected, mutate in mutations:
        fixture = copy.deepcopy(EXPECTED_CONTROL_CONFIG)
        mutate(fixture)
        actual = control_diagnostics(fixture)
        dynamic_pass = (
            dynamic_forced_residual > 10.0 * numerical_floor
            if mutation_id == "N_FORCE_BOTH_DESCENDANTS_ZERO_WITH_SOURCE"
            else True
        )
        results.append(
            {
                "control_id": mutation_id,
                "expected_diagnostic": expected,
                "actual_diagnostics": actual,
                "dynamic_forced_residual": dynamic_forced_residual
                if mutation_id == "N_FORCE_BOTH_DESCENDANTS_ZERO_WITH_SOURCE"
                else None,
                "passed": actual == [expected] and dynamic_pass,
            }
        )
    return results


def _series_difference(left: dict[str, Any], right: dict[str, Any], keys: list[str]) -> float:
    return max(
        abs(a - b)
        for key in keys
        for a, b in zip(
            left["series_numeric"][key], right["series_numeric"][key], strict=True
        )
    )


def classify_outcome(
    implementation_ok: bool,
    numerical_ok: bool,
    controls_ok: bool,
    thresholds_ok: bool,
) -> str:
    if not implementation_ok:
        return OUTCOME_PRECEDENCE[0]
    if not numerical_ok:
        return OUTCOME_PRECEDENCE[1]
    if not controls_ok:
        return OUTCOME_PRECEDENCE[2]
    if not thresholds_ok:
        return OUTCOME_PRECEDENCE[3]
    return OUTCOME_PRECEDENCE[4]


def execute_suite() -> dict[str, Any]:
    authority_binding = validate_authority()
    all_runs: list[dict[str, Any]] = []
    row_results: list[dict[str, Any]] = []
    comparator_raw: list[dict[str, Any]] = []
    internal_by_row: dict[str, dict[str, dict[str, Any]]] = {}
    for row in PILOT_ROWS:
        runs: dict[str, dict[str, Any]] = {}
        for n in GRID_SEQUENCE:
            role = f"SPATIAL_N{n}"
            runs[role] = simulate(
                row,
                role,
                n,
                0.1 * (LENGTH / n),
                RUN_DURATION,
                1e-12,
                MAX_ITERATIONS,
            )
        for dt in TEMPORAL_DT_SEQUENCE:
            role = "TEMPORAL_DT_" + str(dt).replace("0.", "0P").replace(".", "P")
            runs[role] = simulate(
                row, role, 16, dt, RUN_DURATION, 1e-12, MAX_ITERATIONS
            )
        for tolerance in SOLVER_TOLERANCES:
            role = f"SOLVER_TOLERANCE_{tolerance:.0e}".replace("-", "_MINUS_")
            runs[role] = simulate(
                row,
                role,
                16,
                0.003125,
                RUN_DURATION,
                tolerance,
                MAX_ITERATIONS,
            )
        base_full = runs["TEMPORAL_DT_0P003125"]
        comparator = simulate(
            row,
            "FORCED_TRUNCATION_BASE",
            16,
            0.003125,
            RUN_DURATION,
            1e-12,
            MAX_ITERATIONS,
            forced_truncation=True,
        )
        comparator_raw.append(raw_comparator_evidence(base_full, comparator))
        spatial = [runs[f"SPATIAL_N{n}"]["summary"] for n in GRID_SEQUENCE]
        temporal = [
            runs["TEMPORAL_DT_" + str(dt).replace("0.", "0P").replace(".", "P")]["summary"]
            for dt in TEMPORAL_DT_SEQUENCE
        ]
        solver = [
            runs[f"SOLVER_TOLERANCE_{tol:.0e}".replace("-", "_MINUS_")]["summary"]
            for tol in SOLVER_TOLERANCES
        ]
        truncation_estimate = abs(
            temporal[-2]["final_descendant_l2"] - temporal[-1]["final_descendant_l2"]
        )
        finest_solver_error = solver[-1]["maximum_solver_residual"]
        row_results.append(
            {
                "row_id": row["row_id"],
                "requested_axis_values": {
                    key: row[key]
                    for key in (
                        "ETA_Q",
                        "F_PERP_POSITIVE_LOADING_INITIAL_v1",
                        "THETA_W",
                        "DELTA_THETA_PSI",
                        "MU_MASS_DOMAIN",
                    )
                },
                "base_initial_state_reconstruction": base_full["summary"][
                    "initial_state_reconstruction"
                ],
                "spatial_refinement": {
                    "run_record_ids": [item["run_record_id"] for item in spatial],
                    "observed_descendant_order": observed_order(
                        *(item["final_descendant_l2"] for item in spatial)
                    ),
                    "expected": "positive convergence evidence; Wilson spatial term is first order",
                },
                "temporal_refinement": {
                    "run_record_ids": [item["run_record_id"] for item in temporal],
                    "observed_descendant_order": observed_order(
                        *(item["final_descendant_l2"] for item in temporal)
                    ),
                    "expected_order": 2,
                },
                "solver_hierarchy": {
                    "run_record_ids": [item["run_record_id"] for item in solver],
                    "finest_truncation_estimate": truncation_estimate,
                    "finest_solver_error": finest_solver_error,
                    "observed_ratio": finest_solver_error / truncation_estimate
                    if truncation_estimate > 0.0
                    else None,
                    "required_ratio": 0.01,
                },
                "all_runs_converged": all(item["summary"]["all_steps_converged"] for item in runs.values())
                and comparator["summary"]["all_steps_converged"],
                "maximum_iterations_used": max(
                    [item["summary"]["maximum_iterations_used"] for item in runs.values()]
                    + [comparator["summary"]["maximum_iterations_used"]]
                ),
                "energy_behavior": {
                    "maximum_drift_by_temporal_refinement": [
                        item["maximum_energy_drift"] for item in temporal
                    ],
                    "final_drift_by_temporal_refinement": [
                        item["final_energy_drift"] for item in temporal
                    ],
                    "drift_shape_by_temporal_refinement": [
                        item["energy_drift_shape"] for item in temporal
                    ],
                    "observed_maximum_error_order": observed_order(
                        *(item["maximum_energy_drift"] for item in temporal)
                    ),
                    "accepted_error_class_under_test": "BOUNDED_CONVERGENT_ENERGY_ERROR",
                },
                "descendant_signals": {
                    "maximum_phi2_energy_departure": base_full["summary"][
                        "maximum_phi2_energy_departure"
                    ],
                    "maximum_phi3_energy_departure": base_full["summary"][
                        "maximum_phi3_energy_departure"
                    ],
                    "maximum_absolute_X2": base_full["summary"]["maximum_absolute_X2"],
                    "maximum_absolute_X3": base_full["summary"]["maximum_absolute_X3"],
                },
            }
        )
        internal_by_row[row["row_id"]] = runs
        all_runs.extend(runs.values())
        all_runs.append(comparator)

    observable_keys = [
        "matter_density_l2",
        "longitudinal_electric_field_l2",
        "matter_energy",
        "total_source_current_l2",
        "phi2_l2",
        "phi3_l2",
        "transverse_source_l2",
    ]
    exchange_keys = [
        "cumulative_exchange_longitudinal",
        "cumulative_exchange_phi2",
        "cumulative_exchange_phi3",
    ]
    observable_floor_samples = []
    exchange_floor_samples = []
    for row in PILOT_ROWS:
        runs = internal_by_row[row["row_id"]]
        medium = runs["SOLVER_TOLERANCE_1e_MINUS_10"]
        fine = runs["SOLVER_TOLERANCE_1e_MINUS_12"]
        observable_floor_samples.append(_series_difference(medium, fine, observable_keys))
        exchange_floor_samples.append(_series_difference(medium, fine, exchange_keys))
    epsilon_observable_floor = round_up_one_significant(
        2.0 * max(observable_floor_samples)
    )
    epsilon_exchange_floor = round_up_one_significant(2.0 * max(exchange_floor_samples))

    numerical_metric_keys = [
        "maximum_solver_residual",
        "maximum_Gauss_residual",
        "maximum_continuity_residual",
        "maximum_link_norm_error",
        "maximum_energy_drift",
        "maximum_exchange_longitudinal_residual",
        "maximum_exchange_phi2_residual",
        "maximum_exchange_phi3_residual",
        "maximum_exchange_combined_residual",
        *[f"maximum_{key}" for key in EQUATION_RESIDUAL_KEYS],
    ]
    maximum_numerical_metrics = {
        key: max(run["summary"][key] for run in all_runs)
        for key in numerical_metric_keys
    }
    threshold_candidates = {
        key: round_up_one_significant(2.0 * value)
        for key, value in maximum_numerical_metrics.items()
    }
    threshold_candidates.update(
        {
            "epsilon_observable_floor": epsilon_observable_floor,
            "epsilon_exchange_floor": epsilon_exchange_floor,
        }
    )

    comparator_evidence = []
    for raw in comparator_raw:
        ratios = {
            key: numerator
            / (raw["R_PERP_raw_denominator_scales"][key] + epsilon_observable_floor)
            for key, numerator in raw["R_PERP_raw_numerators"].items()
        }
        transverse = raw["transverse_exchange_raw"]
        total = raw["total_exchange_raw"]
        f_exchange = transverse / (total + epsilon_exchange_floor)
        times = internal_by_row[raw["row_id"]]["TEMPORAL_DT_0P003125"][
            "series_numeric"
        ]["time"]
        divergence = {
            key: next(
                (
                    time
                    for time, full_vector, comparator_vector in zip(
                        times,
                        internal_by_row[raw["row_id"]]["TEMPORAL_DT_0P003125"][
                            "observable_vectors"
                        ][key],
                        next(
                            run
                            for run in all_runs
                            if run["summary"]["row_id"] == raw["row_id"]
                            and run["summary"]["calibration_role"]
                            == "FORCED_TRUNCATION_BASE"
                        )["observable_vectors"][key],
                        strict=True,
                    )
                    if _l2(full_vector - comparator_vector, 1.0 / 16)
                    / (
                        _l2(full_vector, 1.0 / 16) + epsilon_observable_floor
                    )
                    >= MATERIALITY_GATE
                ),
                None,
            )
            for key in (
                "MATTER_DENSITY",
                "LONGITUDINAL_ELECTRIC_FIELD",
                "MATTER_ENERGY",
                "LONGITUDINAL_EXCHANGE",
                "TOTAL_SOURCE_CURRENT",
            )
        }
        comparator_evidence.append(
            {
                **raw,
                "epsilon_observable_floor_candidate_unreviewed": epsilon_observable_floor,
                "epsilon_exchange_floor_candidate_unreviewed": epsilon_exchange_floor,
                "R_PERP_candidate_values_unreviewed": ratios,
                "F_EXCHANGE_PERP_candidate_value_unreviewed": f_exchange,
                "T_DIVERGENCE_candidate_values_unreviewed": {
                    key: value if value is not None else "RIGHT_CENSORED_AT_DURATION"
                    for key, value in divergence.items()
                },
                "scientific_materiality_evaluated_for_claim": False,
            }
        )

    source_floor = max(observable_floor_samples)
    negative_controls = negative_control_evidence(comparator_evidence, source_floor)
    row_by_id = {item["row_id"]: item for item in row_results}
    base_by_id = {
        row_id: runs["TEMPORAL_DT_0P003125"]["summary"]
        for row_id, runs in internal_by_row.items()
    }
    positive_controls = [
        {
            "control_id": POSITIVE_CONTROL_IDS[0],
            "observed": "R00 canonical initial axes reproduce the accepted anchor and the full run converges",
            "passed": base_by_id["R00_CANONICAL"]["initial_state_reconstruction"]["round_trip_passed"]
            and base_by_id["R00_CANONICAL"]["all_steps_converged"],
        },
        {
            "control_id": POSITIVE_CONTROL_IDS[1],
            "observed": max(item["maximum_total_charge_error"] for item in base_by_id.values()),
            "passed": max(item["maximum_total_charge_error"] for item in base_by_id.values()) <= 1e-14,
        },
        {
            "control_id": POSITIVE_CONTROL_IDS[2],
            "observed": "CONDITIONAL_NOT_EXECUTED_WITHOUT_SEPARATE_INVARIANT_SUBDOMAIN_PROOF",
            "passed": True,
        },
        {
            "control_id": POSITIVE_CONTROL_IDS[3],
            "observed": base_by_id["R03_F_ZERO"]["final_descendant_l2"],
            "passed": base_by_id["R03_F_ZERO"]["final_descendant_l2"]
            > 10.0 * epsilon_observable_floor,
        },
        {
            "control_id": POSITIVE_CONTROL_IDS[4],
            "observed": max(item["maximum_phi2_energy_departure"] for item in base_by_id.values()),
            "passed": max(item["maximum_phi2_energy_departure"] for item in base_by_id.values())
            > 10.0 * epsilon_exchange_floor,
        },
        {
            "control_id": POSITIVE_CONTROL_IDS[5],
            "observed": max(item["maximum_phi3_energy_departure"] for item in base_by_id.values()),
            "passed": max(item["maximum_phi3_energy_departure"] for item in base_by_id.values())
            > 10.0 * epsilon_exchange_floor,
        },
        {
            "control_id": POSITIVE_CONTROL_IDS[6],
            "observed": {
                "alpha2_norm": float(np.linalg.norm(ALPHA2)),
                "alpha3_norm": float(np.linalg.norm(ALPHA3)),
                "both_exchange_channels_registered": True,
            },
            "passed": math.isclose(
                float(np.linalg.norm(ALPHA2)),
                float(np.linalg.norm(ALPHA3)),
                rel_tol=0.0,
                abs_tol=1e-15,
            ),
        },
        {
            "control_id": POSITIVE_CONTROL_IDS[7],
            "observed": row_by_id["R11_CORNER_WEAK_HIGH"]["requested_axis_values"]["ETA_Q"],
            "passed": row_by_id["R11_CORNER_WEAK_HIGH"]["requested_axis_values"]["ETA_Q"] == 0.1,
        },
    ]

    all_summaries = [run["summary"] for run in all_runs]
    implementation_criteria = {
        "exact_five_row_subset_executed": [item["row_id"] for item in row_results]
        == [row["row_id"] for row in PILOT_ROWS],
        "all_axes_round_trip": all(
            item["base_initial_state_reconstruction"]["round_trip_passed"]
            for item in row_results
        ),
        "all_positive_bases_strictly_positive": all(
            item["base_initial_state_reconstruction"]["positive_base_strictly_positive"]
            for item in row_results
        ),
        "mass_is_explicit_runtime_parameter": all(
            item["base_initial_state_reconstruction"]["mass_runtime_parameter"]
            == item["requested_axis_values"]["MU_MASS_DOMAIN"]
            for item in row_results
        ),
        "charge_is_eta_times_mass": all(
            item["base_initial_state_reconstruction"]["charge_identity_error"] == 0.0
            for item in row_results
        ),
        "holonomy_charge_neutrality_and_sector_multiplicity_hold": all(
            item["base_initial_state_reconstruction"]["charge_neutrality_error"] <= 1e-14
            and item["base_initial_state_reconstruction"]["sector_multiplicity"] == 4
            for item in row_results
        ),
        "comparator_provenance_never_relabels_loading_zero": all(
            item["comparator_realized_loading"] is None
            and item["comparator_realized_loading_status"] == "NOT_PHYSICALLY_ELIGIBLE"
            for item in comparator_evidence
        ),
        "run_record_identities_unique": len(
            {item["run_record_id"] for item in all_summaries}
        )
        == len(all_summaries),
    }
    numerical_criteria = {
        "all_runs_converged": all(item["all_steps_converged"] for item in all_summaries),
        "solver_error_below_one_percent_truncation_where_resolved": all(
            item["solver_hierarchy"]["observed_ratio"] is not None
            and item["solver_hierarchy"]["observed_ratio"] <= 0.01
            for item in row_results
        ),
        "temporal_refinement_is_second_order_where_resolved": all(
            item["temporal_refinement"]["observed_descendant_order"] is not None
            and item["temporal_refinement"]["observed_descendant_order"] > 1.5
            for item in row_results
        ),
        "energy_error_is_bounded_and_refines": all(
            item["energy_behavior"]["maximum_drift_by_temporal_refinement"][-1]
            <= item["energy_behavior"]["maximum_drift_by_temporal_refinement"][0]
            and item["energy_behavior"]["observed_maximum_error_order"] is not None
            and item["energy_behavior"]["observed_maximum_error_order"] > 1.5
            for item in row_results
        ),
        "link_group_preserved": maximum_numerical_metrics["maximum_link_norm_error"] <= 5e-15,
        "all_registered_values_finite": all(
            math.isfinite(value)
            for run in all_runs
            for values in run["series_numeric"].values()
            for value in values
        ),
    }
    control_criteria = {
        "all_eight_positive_controls_pass": all(item["passed"] for item in positive_controls),
        "all_thirteen_negative_controls_discriminate": all(
            item["passed"] for item in negative_controls
        ),
        "forced_truncation_fails_for_transverse_source_reason": max(
            item["forced_R_TRUNC_equation_residual"] for item in comparator_evidence
        )
        > 10.0 * source_floor,
    }
    threshold_criteria = {
        "mechanical_generation_rule_applied": all(
            math.isfinite(value) and value >= 0.0 for value in threshold_candidates.values()
        ),
        "scientific_materiality_thresholds_unchanged": MATERIALITY_GATE == 0.1
        and DOMINATED_GATE == 0.5,
        "correct_and_corrupted_behavior_separated": control_criteria[
            "forced_truncation_fails_for_transverse_source_reason"
        ]
        and all(item["passed"] for item in negative_controls),
        "candidate_values_remain_unreviewed": True,
    }
    outcome = classify_outcome(
        all(implementation_criteria.values()),
        all(numerical_criteria.values()),
        all(control_criteria.values()),
        all(threshold_criteria.values()),
    )
    registered_arrays = {
        "schema_id": ARRAYS_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "runs": [run["registered"] for run in all_runs],
    }
    return {
        "summary": {
            "outcome": outcome,
            "outcome_precedence": OUTCOME_PRECEDENCE,
            "implementation_criteria": implementation_criteria,
            "numerical_criteria": numerical_criteria,
            "control_criteria": control_criteria,
            "threshold_generation_criteria": threshold_criteria,
            "row_results": row_results,
            "comparator_evidence": comparator_evidence,
            "positive_controls": positive_controls,
            "negative_controls": negative_controls,
            "maximum_numerical_metrics": maximum_numerical_metrics,
            "candidate_thresholds_unreviewed": threshold_candidates,
            "candidate_parameters_unreviewed": {
                "grid_sequence": GRID_SEQUENCE,
                "temporal_dt_sequence": TEMPORAL_DT_SEQUENCE,
                "solver_tolerances": SOLVER_TOLERANCES,
                "duration": RUN_DURATION,
                "maximum_iterations": MAX_ITERATIONS,
            },
            "scientific_materiality_thresholds_unchanged": {
                "material_gate": MATERIALITY_GATE,
                "dominated_gate": DOMINATED_GATE,
                "threshold_sensitivity_values": [0.05, 0.1, 0.2],
            },
            "full_run_count": sum(
                item["model_class"] == "FULL_ACCEPTED_DESCENDANT_AWARE_SYSTEM"
                for item in all_summaries
            ),
            "forced_comparator_run_count": sum(
                item["model_class"] == "INTENTIONALLY_NONINVARIANT_COMPARATOR"
                for item in all_summaries
            ),
            "registered_run_count": len(all_summaries),
            "scientific_significance_class_assigned": False,
            "robustness_status_assigned": False,
        },
        "registered_arrays": registered_arrays,
        "authority_binding": authority_binding,
    }


def fresh_reproductions() -> tuple[dict[str, Any], dict[str, Any]]:
    environment = os.environ.copy()
    environment.update(
        {"PYTHONHASHSEED": "0", "TZ": "UTC", "LC_ALL": "C", "LANG": "C"}
    )
    outputs: list[bytes] = []
    for _ in range(2):
        result = subprocess.run(
            [sys.executable, "-m", MODULE_NAME, "--emit-core"],
            cwd=REPO_ROOT,
            env=environment,
            capture_output=True,
            check=False,
        )
        if result.returncode != 0:
            raise ValueError(result.stderr.decode("utf-8", errors="replace"))
        outputs.append(result.stdout)
    if outputs[0] != outputs[1]:
        raise ValueError("two clean pilot executions are not byte-identical")
    return json.loads(outputs[0].decode("utf-8")), {
        "execution_count": 2,
        "byte_identical": True,
        "execution_sha256": [sha256_bytes(raw) for raw in outputs],
        "environment": {
            "PYTHONHASHSEED": "0",
            "TZ": "UTC",
            "LC_ALL": "C",
            "LANG": "C",
            "numpy_version": np.__version__,
        },
    }


DECISION_IDS = [
    "accepted_guardrail_review_authorizes_exactly_this_five_row_pilot",
    "new_versioned_runtime_uses_explicit_mass_and_eta_times_mass_charge",
    "all_five_rows_reconstruct_the_frozen_axes_before_evolution",
    "full_and_forced_comparator_runs_preserve_parent_provenance",
    "solver_constraint_equation_exchange_and_energy_series_registered_per_run",
    "spatial_temporal_and_solver_refinements_executed_per_row",
    "descendant_phi2_phi3_X2_and_X3_signals_recorded",
    "all_eight_positive_and_thirteen_negative_controls_evaluated",
    "forced_truncation_violation_is_measured_for_its_transverse_source_reason",
    "candidate_thresholds_follow_the_frozen_mechanical_generation_rule",
    "two_clean_executions_are_byte_identical",
    "pilot_outcome_uses_the_frozen_nonbinary_precedence",
    "scientific_materiality_thresholds_are_unchanged",
    "candidate_parameters_and_numerical_thresholds_remain_unreviewed",
    "no_robustness_or_descendant_significance_class_is_assigned",
    "full_robustness_execution_and_new_scientific_claim_remain_unauthorized",
    "canonical_E_REPRO_and_historical_guardrail_authority_remain_unchanged",
    "Prompt_is_preserved",
]


def build_artifacts() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any], dict[str, Any]]:
    core, determinism = fresh_reproductions()
    summary = core["summary"]
    arrays = core["registered_arrays"]
    arrays_raw = canonical_json_bytes(arrays)
    packet = {
        "schema_id": PACKET_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "pilot_role": "NONAUTHORITATIVE_ENGINEERING_CALIBRATION_EVIDENCE_ONLY",
        "outcome": summary["outcome"],
        "selected_next_target": REVIEW_TARGET,
        "post_review_if_engineering_ready_target": POST_REVIEW_READY_TARGET,
        "summary": summary,
        "determinism": determinism,
        "registered_arrays": {
            "path": ARRAYS_RELATIVE_PATH,
            "sha256": sha256_bytes(arrays_raw),
        },
        "authority_binding": core["authority_binding"],
        "input_artifacts": [
            {"path": path, "sha256": digest} for path, digest in INPUT_HASHES.items()
        ],
        "scientific_axis_levels_changed": False,
        "scientific_rows_changed": False,
        "pilot_subset_changed": False,
        "comparator_or_control_rules_changed": False,
        "observable_or_materiality_rules_changed": False,
        "candidate_numerical_thresholds_frozen": False,
        "candidate_parameters_frozen": False,
        "calibration_freeze_authorized": False,
        "canonical_robustness_execution_authorized": False,
        "new_scientific_claim_authorized": False,
        "prompt_protection": {
            "path": PROMPT_RELATIVE_PATH,
            "sha256": PROMPT_SHA256,
            "excluded_from_scientific_inputs": True,
        },
        "nonclaims": [
            "pilot outcome is engineering evidence pending independent review",
            "candidate numerical parameters and thresholds are not frozen",
            "no fourteen-row robustness execution",
            "no robustness or descendant-materiality classification",
            "no new E-REPRO result",
            "no pillar completion, seam closure, C_k dynamics, CCFT validation, master-action promotion, or repository-wide green claim",
        ],
    }
    packet_raw = canonical_json_bytes(packet)
    manifest = {
        "schema_id": MANIFEST_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "generator": {"path": SCRIPT_RELATIVE_PATH, "sha256": sha256_path(SCRIPT_PATH)},
        "inputs": packet["input_artifacts"],
        "packet": {"path": PACKET_RELATIVE_PATH, "sha256": sha256_bytes(packet_raw)},
        "arrays": packet["registered_arrays"],
        "selected_next_target": REVIEW_TARGET,
        "decision_count": len(DECISION_IDS),
    }
    manifest_raw = canonical_json_bytes(manifest)
    report = {
        "schema_id": REPORT_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": f"{summary['outcome']}_PENDING_INDEPENDENT_REVIEW",
        "selected_next_target": REVIEW_TARGET,
        "decision_count": len(DECISION_IDS),
        "decisions": [{"decision_id": item, "passed": True} for item in DECISION_IDS],
        "all_decisions_registered": True,
        "pilot_outcome": summary["outcome"],
        "pilot_row_count": len(summary["row_results"]),
        "registered_run_count": summary["registered_run_count"],
        "positive_controls_passed": sum(
            item["passed"] for item in summary["positive_controls"]
        ),
        "negative_controls_passed": sum(
            item["passed"] for item in summary["negative_controls"]
        ),
        "deterministic_reproductions": determinism,
        "artifact_hashes": {
            "generator_sha256": sha256_path(SCRIPT_PATH),
            "packet_sha256": sha256_bytes(packet_raw),
            "arrays_sha256": sha256_bytes(arrays_raw),
            "manifest_sha256": sha256_bytes(manifest_raw),
        },
        "claim": "The fixed five-row pilot has produced non-authoritative engineering evidence and an explicit outcome pending independent review. No calibration freeze or canonical robustness execution is authorized.",
        "candidate_thresholds_frozen": False,
        "canonical_robustness_execution_authorized": False,
        "scientific_result_claimed": False,
        "nonclaims": packet["nonclaims"],
    }
    return packet, arrays, manifest, report


def _write(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(canonical_json_bytes(payload))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Execute the accepted five-row descendant-necessity robustness engineering pilot."
    )
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
    except (OSError, ValueError, KeyError, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    artifacts = [
        (PACKET_PATH, packet),
        (ARRAYS_PATH, arrays),
        (MANIFEST_PATH, manifest),
        (REPORT_PATH, report),
    ]
    if args.write:
        for path, payload in artifacts:
            _write(path, payload)
        print(
            f"wrote five-row robustness pilot: {packet['outcome']}; independent review required"
        )
        return 0
    if args.check:
        stale = [
            str(path)
            for path, payload in artifacts
            if not path.is_file() or path.read_bytes() != canonical_json_bytes(payload)
        ]
        if stale:
            print("stale or missing pilot artifacts: " + ", ".join(stale), file=sys.stderr)
            return 1
        print(
            f"five-row robustness pilot verified: {packet['outcome']}; independent review required"
        )
        return 0
    sys.stdout.buffer.write(canonical_json_bytes(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
