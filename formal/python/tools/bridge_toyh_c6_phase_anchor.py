from __future__ import annotations

"""Toy-H <-> C6 phase-anchor compatibility proxy (quarantine-safe).

Goal
- Provide a deterministic, bounded phase-anchor observable that remains
  sensitive at very small global phase shifts and complements the existing
  Toy-H phase-channel control.
"""

import numpy as np

from formal.python.crft.cp_nlse_2d import (
    CPParams2D,
    Grid2D,
    compute_energy_2d,
    compute_norm_2d,
    rhs_cp_nlse_2d,
)


def _q(x: float, *, sig: int = 12) -> float:
    return float(f"{float(x):.{int(sig)}g}")


def _principal_angle(x: float) -> float:
    return float((float(x) + np.pi) % (2.0 * np.pi) - np.pi)


def _angle_to_phasor(phi: float) -> complex:
    return complex(np.cos(float(phi)), np.sin(float(phi)))


def _phasor_dist(u1: complex, u2: complex) -> float:
    return float(abs(complex(u1) - complex(u2)))


def _phase_residual_stable(phi1: float, phi2: float) -> float:
    return _phasor_dist(_angle_to_phasor(phi1), _angle_to_phasor(phi2))


def _stable_equivariance_phase_residual(*, base: np.ndarray, transformed: np.ndarray, theta: float) -> float:
    denom = max(float(np.vdot(base, base).real), 1e-12)
    alpha = complex(np.vdot(base, transformed) / denom)
    alpha_mag = max(abs(alpha), 1e-12)
    alpha_unit = alpha / alpha_mag
    target_unit = _angle_to_phasor(theta)
    return _phasor_dist(alpha_unit, target_unit)


def _plane_wave(grid: Grid2D, rho0: float, kx_idx: int = 1, ky_idx: int = 0) -> np.ndarray:
    kx = 2.0 * np.pi * kx_idx / grid.Lx
    ky = 2.0 * np.pi * ky_idx / grid.Ly
    return np.sqrt(rho0) * np.exp(1j * (kx * grid.x + ky * grid.y))


def evaluate_toyh_c6_phase_anchor(
    *,
    theta: float,
    grid_n: int,
    amplitude_scale: float = 1.0,
    tol_invariance: float = 1e-10,
    tol_phase_anchor: float = 1e-9,
    min_anchor_magnitude: float = 1e-8,
    anchor_sign: float = 1.0,
    use_stable_invariance: bool = False,
) -> dict:
    grid = Grid2D.from_box(Nx=int(grid_n), Ny=int(grid_n), Lx=2.0 * np.pi, Ly=2.0 * np.pi)
    params = CPParams2D(g_eff=9.8696, rho0=1.0)

    phi0 = _plane_wave(grid, params.rho0)
    phi1 = float(amplitude_scale) * phi0 * np.exp(1j * float(theta))

    n0 = compute_norm_2d(phi0, grid)
    n1 = compute_norm_2d(phi1, grid)
    e0 = compute_energy_2d(phi0, grid, params)
    e1 = compute_energy_2d(phi1, grid, params)

    rhs0 = rhs_cp_nlse_2d(phi0, grid, params)
    rhs1 = rhs_cp_nlse_2d(phi1, grid, params)
    rhs_equiv = rhs1 * np.exp(-1j * float(theta))
    rhs_rel_legacy = float(np.linalg.norm(rhs_equiv - rhs0) / max(1e-12, np.linalg.norm(rhs0)))
    rhs_phase_residual = _stable_equivariance_phase_residual(base=rhs0, transformed=rhs1, theta=float(theta))
    phase_field_residual = _stable_equivariance_phase_residual(base=phi0, transformed=phi1, theta=float(theta))

    norm_rel = float(abs(n1 - n0) / max(1e-12, abs(n0)))
    energy_rel = float(abs(e1 - e0) / max(1e-12, abs(e0)))
    rhs_rel = rhs_phase_residual if bool(use_stable_invariance) else rhs_rel_legacy
    invariance_residual = max(norm_rel, energy_rel, rhs_rel)
    if bool(use_stable_invariance):
        invariance_residual = max(norm_rel, energy_rel, phase_field_residual, rhs_phase_residual)
    invariance_ok = bool(invariance_residual <= float(tol_invariance))

    overlap = np.mean(np.conjugate(phi0) * phi1)
    anchor_phase = float(np.angle(float(anchor_sign) * overlap))
    anchor_phase_error = float(abs(_principal_angle(anchor_phase - float(theta))))
    baseline_mag = float(np.mean(np.abs(phi0) ** 2))
    anchor_magnitude_ratio = float(abs(overlap) / max(1e-12, baseline_mag))

    phase_anchor_ok = bool(anchor_phase_error <= float(tol_phase_anchor))
    anchor_magnitude_ok = bool(anchor_magnitude_ratio >= float(min_anchor_magnitude))
    admissible = bool(invariance_ok and phase_anchor_ok and anchor_magnitude_ok)

    if not invariance_ok:
        reason = "FAIL_PHASE_INVARIANCE_TOL"
    elif not anchor_magnitude_ok:
        reason = "FAIL_ANCHOR_MAGNITUDE_MIN"
    elif not phase_anchor_ok:
        reason = "FAIL_ANCHOR_PHASE_MISMATCH"
    else:
        reason = "PASS_PHASE_ANCHOR"

    return {
        "schema_version": 1,
        "observable_id": "TOYH_C6_phase_anchor_proxy_v1",
        "inputs": {
            "theta": _q(theta),
            "grid_n": int(grid_n),
            "amplitude_scale": _q(amplitude_scale),
            "tol_invariance": _q(tol_invariance),
            "tol_phase_anchor": _q(tol_phase_anchor),
            "min_anchor_magnitude": _q(min_anchor_magnitude),
            "anchor_sign": _q(anchor_sign),
            "use_stable_invariance": bool(use_stable_invariance),
        },
        "metrics": {
            "norm_rel": _q(norm_rel),
            "energy_rel": _q(energy_rel),
            "rhs_rel": _q(rhs_rel),
            "rhs_rel_legacy": _q(rhs_rel_legacy),
            "rhs_phase_residual": _q(rhs_phase_residual),
            "phase_field_residual": _q(phase_field_residual),
            "invariance_residual": _q(invariance_residual),
            "anchor_phase": _q(anchor_phase),
            "anchor_phase_error": _q(anchor_phase_error),
            "anchor_magnitude_ratio": _q(anchor_magnitude_ratio),
        },
        "status": {
            "invariance_ok": bool(invariance_ok),
            "phase_anchor_ok": bool(phase_anchor_ok),
            "anchor_magnitude_ok": bool(anchor_magnitude_ok),
            "admissible": bool(admissible),
        },
        "reason_code": reason,
        "specimen_digest": {
            "real0_origin": _q(float(phi0.real[0, 0])),
            "real1_origin": _q(float(phi1.real[0, 0])),
            "phase0_origin": _q(float(np.angle(phi0[0, 0]))),
            "phase1_origin": _q(float(np.angle(phi1[0, 0]))),
        },
    }
