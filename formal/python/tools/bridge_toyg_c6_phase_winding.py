from __future__ import annotations

"""Toy-G <-> C6 phase-winding quantization proxy (quarantine-safe).

Goal
- Provide a deterministic, bounded integer-attractor observable for the first
  Toy-G bridge lane on the C6 canonical surface.
"""

import numpy as np

from formal.python.crft.cp_nlse_2d import CPParams2D, Grid2D


def _q(x: float, *, sig: int = 12) -> float:
    return float(f"{float(x):.{int(sig)}g}")


def _principal_delta(dtheta: np.ndarray) -> np.ndarray:
    return (dtheta + np.pi) % (2.0 * np.pi) - np.pi


def _plane_wave_loop_specimen(
    *,
    grid_n: int,
    loop_length: float,
    winding_target: float,
    amplitude_mod_eps: float,
) -> tuple[np.ndarray, np.ndarray]:
    grid = Grid2D.from_box(Nx=int(grid_n), Ny=int(grid_n), Lx=float(loop_length), Ly=float(loop_length))
    params = CPParams2D(g_eff=9.8696, rho0=1.0)

    x_core = np.asarray(grid.x[:, 0], dtype=float)
    x_loop = np.concatenate([x_core, np.array([float(loop_length)], dtype=float)])
    phase = (2.0 * np.pi * float(winding_target) / float(loop_length)) * x_loop
    amp = 1.0 + float(amplitude_mod_eps) * np.sin(2.0 * np.pi * x_loop / float(loop_length))

    psi_loop = np.sqrt(params.rho0) * amp * np.exp(1j * phase)
    return x_loop, psi_loop


def evaluate_toyg_c6_phase_winding(
    *,
    grid_n: int,
    loop_length: float,
    winding_target: float,
    tol_winding: float,
    unwrap_margin: float,
    amplitude_mod_eps: float = 0.0,
) -> dict:
    x_loop, psi_loop = _plane_wave_loop_specimen(
        grid_n=int(grid_n),
        loop_length=float(loop_length),
        winding_target=float(winding_target),
        amplitude_mod_eps=float(amplitude_mod_eps),
    )

    theta = np.angle(psi_loop)
    delta = _principal_delta(np.diff(theta))
    total_phase = float(np.sum(delta))
    raw_winding = float(total_phase / (2.0 * np.pi))
    nearest_int = int(np.rint(raw_winding))
    integer_distance = float(abs(raw_winding - float(nearest_int)))
    max_abs_delta = float(np.max(np.abs(delta)))

    unwrap_limit = float(np.pi - float(unwrap_margin))
    unwrap_guard_ok = bool(max_abs_delta <= unwrap_limit)
    integer_close = bool(integer_distance <= float(tol_winding))
    admissible = bool(unwrap_guard_ok and integer_close)

    if not unwrap_guard_ok:
        reason = "fail_unwrap_discontinuity_guard"
    elif not integer_close:
        reason = "fail_not_integer_close"
    else:
        reason = f"pass_quantized_winding_{nearest_int}"

    return {
        "schema_version": 1,
        "observable_id": "TOYG_C6_phase_winding_quantization_v1",
        "inputs": {
            "grid_n": int(grid_n),
            "loop_length": _q(loop_length),
            "winding_target": _q(winding_target),
            "k_value": _q((2.0 * np.pi * float(winding_target)) / float(loop_length)),
            "tol_winding": _q(tol_winding),
            "unwrap_margin": _q(unwrap_margin),
            "amplitude_mod_eps": _q(amplitude_mod_eps),
        },
        "metrics": {
            "total_phase_advance": _q(total_phase),
            "raw_winding": _q(raw_winding),
            "nearest_int": int(nearest_int),
            "integer_distance": _q(integer_distance),
            "max_abs_delta": _q(max_abs_delta),
            "unwrap_guard_limit": _q(unwrap_limit),
        },
        "status": {
            "integer_close": bool(integer_close),
            "unwrap_guard_ok": bool(unwrap_guard_ok),
            "admissible": bool(admissible),
        },
        "reason_code": reason,
        "specimen_digest": {
            "x0": _q(float(x_loop[0])),
            "xN": _q(float(x_loop[-1])),
            "phase0": _q(float(theta[0])),
            "phaseN": _q(float(theta[-1])),
        },
    }
