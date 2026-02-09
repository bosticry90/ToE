from __future__ import annotations

"""Toy-H <-> C6 current-anchor compatibility proxy (quarantine-safe).

Goal
- Provide a deterministic, bounded current-anchor observable that resolves
  tiny local-phase-shear control probes while preserving fail-closed behavior
  on invariance and wrong-operator controls.
"""

import numpy as np

from formal.python.crft.cp_nlse_2d import CPParams2D, Grid2D, grad2_2d


def _q(x: float, *, sig: int = 12) -> float:
    return float(f"{float(x):.{int(sig)}g}")


def _plane_wave(grid: Grid2D, rho0: float, kx_idx: int = 1, ky_idx: int = 0) -> np.ndarray:
    kx = 2.0 * np.pi * kx_idx / grid.Lx
    ky = 2.0 * np.pi * ky_idx / grid.Ly
    return np.sqrt(rho0) * np.exp(1j * (kx * grid.x + ky * grid.y))


def _current_l2(phi: np.ndarray, grid: Grid2D) -> float:
    phi_x, phi_y = grad2_2d(phi, grid)
    jx = np.imag(np.conjugate(phi) * phi_x)
    jy = np.imag(np.conjugate(phi) * phi_y)
    return float(np.sum((jx * jx + jy * jy).real) * grid.dx * grid.dy)


def _mean_current_x(phi: np.ndarray, grid: Grid2D) -> float:
    phi_x, _ = grad2_2d(phi, grid)
    jx = np.imag(np.conjugate(phi) * phi_x)
    mass = float(np.sum((np.abs(phi) ** 2).real) * grid.dx * grid.dy)
    return float(np.sum(jx.real) * grid.dx * grid.dy / max(1e-12, mass))


def _phase_shear_slope(*, phi0: np.ndarray, phi_shear: np.ndarray, grid: Grid2D) -> float:
    ratio = np.asarray(phi_shear / np.where(np.abs(phi0) > 0.0, phi0, 1.0 + 0.0j), dtype=np.complex128)
    phase_line = np.unwrap(np.angle(ratio[:, 0]))
    x_line = np.asarray(grid.x[:, 0], dtype=float)

    x_centered = x_line - float(np.mean(x_line))
    phase_centered = phase_line - float(np.mean(phase_line))
    denom = float(np.dot(x_centered, x_centered))
    if denom <= 0.0:
        return 0.0
    return float(np.dot(x_centered, phase_centered) / denom)


def evaluate_toyh_c6_current_anchor(
    *,
    theta: float,
    grid_n: int,
    amplitude_scale: float = 1.0,
    local_phase_shear_alpha: float = 0.5,
    tol_invariance: float = 1e-10,
    tol_current_anchor: float = 1e-7,
    min_anchor_response: float = 1e-8,
    anchor_sign: float = 1.0,
) -> dict:
    grid = Grid2D.from_box(Nx=int(grid_n), Ny=int(grid_n), Lx=2.0 * np.pi, Ly=2.0 * np.pi)
    params = CPParams2D(g_eff=9.8696, rho0=1.0)

    phi0 = _plane_wave(grid, params.rho0)
    phi1 = float(amplitude_scale) * phi0 * np.exp(1j * float(theta))
    phi_shear = phi0 * np.exp(1j * float(local_phase_shear_alpha) * grid.x)

    c0 = _current_l2(phi0, grid)
    c1 = _current_l2(phi1, grid)
    current_l2_rel = float(abs(c1 - c0) / max(1e-12, abs(c0)))
    invariance_ok = bool(current_l2_rel <= float(tol_invariance))

    px0 = _mean_current_x(phi0, grid)
    px_shear = _mean_current_x(phi_shear, grid)
    anchor_delta = _phase_shear_slope(phi0=phi0, phi_shear=phi_shear, grid=grid)
    anchor_response = float(abs(anchor_delta))
    anchor_error = float(abs(float(anchor_sign) * anchor_delta - float(local_phase_shear_alpha)))

    anchor_response_ok = bool(anchor_response >= float(min_anchor_response))
    anchor_match_ok = bool(anchor_error <= float(tol_current_anchor))
    admissible = bool(invariance_ok and anchor_response_ok and anchor_match_ok)

    if not invariance_ok:
        reason = "FAIL_CURRENT_INVARIANCE_TOL"
    elif not anchor_response_ok:
        reason = "FAIL_CURRENT_ANCHOR_RESPONSE_MIN"
    elif not anchor_match_ok:
        reason = "FAIL_CURRENT_ANCHOR_MISMATCH"
    else:
        reason = "PASS_CURRENT_ANCHOR"

    return {
        "schema_version": 1,
        "observable_id": "TOYH_C6_current_anchor_proxy_v1",
        "inputs": {
            "theta": _q(theta),
            "grid_n": int(grid_n),
            "amplitude_scale": _q(amplitude_scale),
            "local_phase_shear_alpha": _q(local_phase_shear_alpha),
            "tol_invariance": _q(tol_invariance),
            "tol_current_anchor": _q(tol_current_anchor),
            "min_anchor_response": _q(min_anchor_response),
            "anchor_sign": _q(anchor_sign),
        },
        "metrics": {
            "current_l2_rel": _q(current_l2_rel),
            "anchor_delta": _q(anchor_delta),
            "anchor_response": _q(anchor_response),
            "anchor_error": _q(anchor_error),
            "current_x_baseline": _q(px0),
            "current_x_shear": _q(px_shear),
        },
        "status": {
            "invariance_ok": bool(invariance_ok),
            "anchor_response_ok": bool(anchor_response_ok),
            "anchor_match_ok": bool(anchor_match_ok),
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
