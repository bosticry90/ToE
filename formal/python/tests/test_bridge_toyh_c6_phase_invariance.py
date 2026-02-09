from __future__ import annotations

import numpy as np

from formal.python.crft.cp_nlse_2d import (
    CPParams2D,
    Grid2D,
    compute_energy_2d,
    compute_norm_2d,
    rhs_cp_nlse_2d,
)


def _plane_wave(grid: Grid2D, rho0: float, kx_idx: int = 1, ky_idx: int = 0) -> np.ndarray:
    kx = 2.0 * np.pi * kx_idx / grid.Lx
    ky = 2.0 * np.pi * ky_idx / grid.Ly
    return np.sqrt(rho0) * np.exp(1j * (kx * grid.x + ky * grid.y))


def _metrics(*, theta: float, Nx: int) -> dict:
    Ny = Nx
    grid = Grid2D.from_box(Nx=Nx, Ny=Ny, Lx=2.0 * np.pi, Ly=2.0 * np.pi)
    params = CPParams2D(g_eff=9.8696, rho0=1.0)

    phi0 = _plane_wave(grid, params.rho0)
    phi1 = phi0 * np.exp(1j * theta)

    n0 = compute_norm_2d(phi0, grid)
    n1 = compute_norm_2d(phi1, grid)
    e0 = compute_energy_2d(phi0, grid, params)
    e1 = compute_energy_2d(phi1, grid, params)

    rhs0 = rhs_cp_nlse_2d(phi0, grid, params)
    rhs1 = rhs_cp_nlse_2d(phi1, grid, params)
    rhs_equiv = rhs1 * np.exp(-1j * theta)
    rhs_rel = float(np.linalg.norm(rhs_equiv - rhs0) / np.linalg.norm(rhs0))

    return {
        "norm_rel": float(abs(n1 - n0) / n0),
        "energy_rel": float(abs(e1 - e0) / max(1e-12, abs(e0))),
        "rhs_rel": rhs_rel,
        "real0_at_origin": float(phi0.real[0, 0]),
        "real1_at_origin": float(phi1.real[0, 0]),
    }


def test_bridge_toyh_c6_phase_invariance_deterministic() -> None:
    theta = float(np.pi / 3.0)
    m1 = _metrics(theta=theta, Nx=16)
    m2 = _metrics(theta=theta, Nx=16)
    assert m1 == m2


def test_bridge_toyh_c6_phase_invariance_invariant_observables() -> None:
    theta = float(np.pi / 3.0)
    metrics = _metrics(theta=theta, Nx=16)
    tol = 1e-10

    assert metrics["norm_rel"] <= tol
    assert metrics["energy_rel"] <= tol
    assert metrics["rhs_rel"] <= tol


def test_bridge_toyh_c6_phase_invariance_negative_control_amplitude_scaling() -> None:
    grid = Grid2D.from_box(Nx=16, Ny=16, Lx=2.0 * np.pi, Ly=2.0 * np.pi)
    params = CPParams2D(g_eff=9.8696, rho0=1.0)

    phi0 = _plane_wave(grid, params.rho0)
    phi_bad = 1.1 * phi0

    n0 = compute_norm_2d(phi0, grid)
    n1 = compute_norm_2d(phi_bad, grid)

    rel = abs(n1 - n0) / n0
    assert rel > 1e-3


def test_bridge_toyh_c6_phase_invariance_negative_control_phase_sensitive_observable() -> None:
    theta = float(np.pi / 3.0)
    metrics = _metrics(theta=theta, Nx=16)

    delta = abs(metrics["real1_at_origin"] - metrics["real0_at_origin"])
    assert delta > 1e-3


def test_bridge_toyh_c6_phase_invariance_resolution_scan() -> None:
    theta = float(np.pi / 3.0)
    tol = 1e-10

    for n in [8, 12, 16]:
        metrics = _metrics(theta=theta, Nx=n)
        assert metrics["norm_rel"] <= tol
        assert metrics["energy_rel"] <= tol
        assert metrics["rhs_rel"] <= tol
