from __future__ import annotations

"""Toy-G <-> C6 unwrap-stability proxy (quarantine-safe).

Goal
- Provide a deterministic, bounded unwrap-stability observable for the third
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
    unwrap_target: float,
    amplitude_mod_eps: float,
    phase_shear_eps: float,
) -> tuple[np.ndarray, np.ndarray]:
    grid = Grid2D.from_box(Nx=int(grid_n), Ny=int(grid_n), Lx=float(loop_length), Ly=float(loop_length))
    params = CPParams2D(g_eff=9.8696, rho0=1.0)

    x_loop = np.asarray(grid.x[:, 0], dtype=float)
    phase_linear = (2.0 * np.pi * float(unwrap_target) / float(loop_length)) * x_loop
    phase_shear = float(phase_shear_eps) * np.sin(4.0 * np.pi * x_loop / float(loop_length))
    amp = 1.0 + float(amplitude_mod_eps) * np.sin(2.0 * np.pi * x_loop / float(loop_length))

    psi_loop = np.sqrt(params.rho0) * amp * np.exp(1j * (phase_linear + phase_shear))
    return x_loop, psi_loop


def evaluate_toyg_c6_unwrap_stability(
    *,
    grid_n: int,
    loop_length: float,
    unwrap_target: float,
    tol_step_mean: float,
    tol_step_std: float,
    min_near_pi_fraction: float,
    pi_edge_eps: float,
    amplitude_mod_eps: float = 0.0,
    phase_shear_eps: float = 0.0,
) -> dict:
    x_loop, psi_loop = _plane_wave_loop_specimen(
        grid_n=int(grid_n),
        loop_length=float(loop_length),
        unwrap_target=float(unwrap_target),
        amplitude_mod_eps=float(amplitude_mod_eps),
        phase_shear_eps=float(phase_shear_eps),
    )

    theta = np.angle(psi_loop)
    delta = _principal_delta(np.roll(theta, -1) - theta)
    abs_delta = np.abs(delta)
    # The periodic closure edge can introduce a single degenerate step; drop the
    # smallest-magnitude increment deterministically before stability statistics.
    abs_delta_sorted = np.sort(abs_delta)
    core_abs_delta = abs_delta_sorted[1:] if abs_delta_sorted.size > 1 else abs_delta_sorted

    expected_abs_step = float(abs((2.0 * np.pi * float(unwrap_target)) / float(grid_n)))
    mean_abs_step = float(np.mean(core_abs_delta))
    step_std = float(np.std(core_abs_delta))
    near_pi_fraction = float(np.mean(core_abs_delta >= (np.pi - float(pi_edge_eps))))
    mean_abs_step_error = float(abs(mean_abs_step - expected_abs_step))

    near_pi_sensitive = bool(near_pi_fraction >= float(min_near_pi_fraction))
    step_mean_ok = bool(mean_abs_step_error <= float(tol_step_mean))
    step_std_ok = bool(step_std <= float(tol_step_std))
    admissible = bool(near_pi_sensitive and step_mean_ok and step_std_ok)

    if not near_pi_sensitive:
        reason = "fail_not_boundary_sensitive"
    elif not step_std_ok:
        reason = "fail_unwrap_step_variance_high"
    elif not step_mean_ok:
        reason = "fail_unwrap_step_mean_mismatch"
    else:
        reason = "pass_unwrap_stable_boundary"

    return {
        "schema_version": 1,
        "observable_id": "TOYG_C6_unwrap_stability_proxy_v1",
        "inputs": {
            "grid_n": int(grid_n),
            "loop_length": _q(loop_length),
            "unwrap_target": _q(unwrap_target),
            "k_value": _q((2.0 * np.pi * float(unwrap_target)) / float(loop_length)),
            "tol_step_mean": _q(tol_step_mean),
            "tol_step_std": _q(tol_step_std),
            "min_near_pi_fraction": _q(min_near_pi_fraction),
            "pi_edge_eps": _q(pi_edge_eps),
            "amplitude_mod_eps": _q(amplitude_mod_eps),
            "phase_shear_eps": _q(phase_shear_eps),
        },
        "metrics": {
            "expected_abs_step": _q(expected_abs_step),
            "mean_abs_step": _q(mean_abs_step),
            "mean_abs_step_error": _q(mean_abs_step_error),
            "step_std": _q(step_std),
            "near_pi_fraction": _q(near_pi_fraction),
        },
        "status": {
            "near_pi_sensitive": bool(near_pi_sensitive),
            "step_mean_ok": bool(step_mean_ok),
            "step_std_ok": bool(step_std_ok),
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
