from __future__ import annotations

"""Toy-G <-> C6 mode-index quantization proxy (quarantine-safe).

Goal
- Provide a deterministic, bounded integer-attractor observable for the second
  Toy-G bridge lane on the C6 canonical surface.
"""

import numpy as np

from formal.python.crft.cp_nlse_2d import CPParams2D, Grid2D


def _q(x: float, *, sig: int = 12) -> float:
    return float(f"{float(x):.{int(sig)}g}")


def _signed_fft_index(idx: int, n: int) -> int:
    idx = int(idx)
    n = int(n)
    return idx if idx <= (n // 2) else idx - n


def _plane_wave_loop_specimen(
    *,
    grid_n: int,
    loop_length: float,
    mode_target: float,
    amplitude_mod_eps: float,
) -> tuple[np.ndarray, np.ndarray]:
    grid = Grid2D.from_box(Nx=int(grid_n), Ny=int(grid_n), Lx=float(loop_length), Ly=float(loop_length))
    params = CPParams2D(g_eff=9.8696, rho0=1.0)

    x_loop = np.asarray(grid.x[:, 0], dtype=float)
    phase = (2.0 * np.pi * float(mode_target) / float(loop_length)) * x_loop
    amp = 1.0 + float(amplitude_mod_eps) * np.sin(2.0 * np.pi * x_loop / float(loop_length))

    psi_loop = np.sqrt(params.rho0) * amp * np.exp(1j * phase)
    return x_loop, psi_loop


def evaluate_toyg_c6_mode_index_quantization(
    *,
    grid_n: int,
    loop_length: float,
    mode_target: float,
    tol_mode: float,
    min_peak_fraction: float,
    amplitude_mod_eps: float = 0.0,
) -> dict:
    x_loop, psi_loop = _plane_wave_loop_specimen(
        grid_n=int(grid_n),
        loop_length=float(loop_length),
        mode_target=float(mode_target),
        amplitude_mod_eps=float(amplitude_mod_eps),
    )

    spectrum = np.fft.fft(np.asarray(psi_loop, dtype=np.complex128))
    power = np.abs(spectrum) ** 2
    total_power = float(np.sum(power))

    peak_bin = int(np.argmax(power))
    peak_index_signed = int(_signed_fft_index(peak_bin, int(grid_n)))
    peak_fraction = float(power[peak_bin] / max(1e-30, total_power))

    nearest_int = int(np.rint(float(mode_target)))
    integer_distance = float(abs(float(mode_target) - float(nearest_int)))

    integer_close = bool(integer_distance <= float(tol_mode))
    index_match = bool(peak_index_signed == nearest_int)
    peak_fraction_ok = bool(peak_fraction >= float(min_peak_fraction))
    admissible = bool(integer_close and index_match and peak_fraction_ok)

    if not peak_fraction_ok:
        reason = "fail_peak_fraction_low"
    elif not integer_close:
        reason = "fail_not_integer_close"
    elif not index_match:
        reason = "fail_mode_index_mismatch"
    else:
        reason = f"pass_mode_index_{nearest_int}"

    return {
        "schema_version": 1,
        "observable_id": "TOYG_C6_mode_index_quantization_v1",
        "inputs": {
            "grid_n": int(grid_n),
            "loop_length": _q(loop_length),
            "mode_target": _q(mode_target),
            "k_value": _q((2.0 * np.pi * float(mode_target)) / float(loop_length)),
            "tol_mode": _q(tol_mode),
            "min_peak_fraction": _q(min_peak_fraction),
            "amplitude_mod_eps": _q(amplitude_mod_eps),
        },
        "metrics": {
            "peak_bin": int(peak_bin),
            "peak_index_signed": int(peak_index_signed),
            "nearest_int": int(nearest_int),
            "peak_fraction": _q(peak_fraction),
            "integer_distance": _q(integer_distance),
        },
        "status": {
            "integer_close": bool(integer_close),
            "index_match": bool(index_match),
            "peak_fraction_ok": bool(peak_fraction_ok),
            "admissible": bool(admissible),
        },
        "reason_code": reason,
        "specimen_digest": {
            "x0": _q(float(x_loop[0])),
            "xN": _q(float(x_loop[-1])),
            "phase0": _q(float(np.angle(psi_loop[0]))),
            "phaseN": _q(float(np.angle(psi_loop[-1]))),
        },
    }
