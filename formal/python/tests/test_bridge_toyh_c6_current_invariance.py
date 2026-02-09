from __future__ import annotations

import numpy as np

from formal.python.crft.cp_nlse_2d import CPParams2D, Grid2D, grad2_2d


def _plane_wave(grid: Grid2D, rho0: float, kx_idx: int = 1, ky_idx: int = 0) -> np.ndarray:
    kx = 2.0 * np.pi * kx_idx / grid.Lx
    ky = 2.0 * np.pi * ky_idx / grid.Ly
    return np.sqrt(rho0) * np.exp(1j * (kx * grid.x + ky * grid.y))


def _current_l2(phi: np.ndarray, grid: Grid2D) -> float:
    phi_x, phi_y = grad2_2d(phi, grid)
    jx = np.imag(np.conjugate(phi) * phi_x)
    jy = np.imag(np.conjugate(phi) * phi_y)
    return float(np.sum((jx * jx + jy * jy).real) * grid.dx * grid.dy)


def _metrics(*, theta: float, Nx: int, alpha: float = 0.5) -> dict:
    Ny = Nx
    grid = Grid2D.from_box(Nx=Nx, Ny=Ny, Lx=2.0 * np.pi, Ly=2.0 * np.pi)
    params = CPParams2D(g_eff=9.8696, rho0=1.0)

    phi0 = _plane_wave(grid, params.rho0)
    phi1 = phi0 * np.exp(1j * theta)

    current0 = _current_l2(phi0, grid)
    current1 = _current_l2(phi1, grid)

    phi_local_phase_shear = phi0 * np.exp(1j * alpha * grid.x)
    current_local_phase_shear = _current_l2(phi_local_phase_shear, grid)

    return {
        "current_l2_rel": float(abs(current1 - current0) / max(1e-12, abs(current0))),
        "local_phase_shear_rel": float(
            abs(current_local_phase_shear - current0) / max(1e-12, abs(current0))
        ),
    }


def test_bridge_toyh_c6_current_invariance_deterministic() -> None:
    theta = float(np.pi / 3.0)
    m1 = _metrics(theta=theta, Nx=16)
    m2 = _metrics(theta=theta, Nx=16)
    assert m1 == m2


def test_bridge_toyh_c6_current_invariance_invariant_observables() -> None:
    theta = float(np.pi / 3.0)
    metrics = _metrics(theta=theta, Nx=16)
    tol = 1e-10

    assert metrics["current_l2_rel"] <= tol


def test_bridge_toyh_c6_current_invariance_negative_control_amplitude_scaling() -> None:
    grid = Grid2D.from_box(Nx=16, Ny=16, Lx=2.0 * np.pi, Ly=2.0 * np.pi)
    params = CPParams2D(g_eff=9.8696, rho0=1.0)

    phi0 = _plane_wave(grid, params.rho0)
    phi_bad = 1.1 * phi0

    c0 = _current_l2(phi0, grid)
    c1 = _current_l2(phi_bad, grid)

    rel = abs(c1 - c0) / max(1e-12, abs(c0))
    assert rel > 1e-3


def test_bridge_toyh_c6_current_invariance_negative_control_local_phase_shear() -> None:
    theta = float(np.pi / 3.0)
    metrics = _metrics(theta=theta, Nx=16)
    assert metrics["local_phase_shear_rel"] > 1e-3


def test_bridge_toyh_c6_current_invariance_resolution_scan() -> None:
    theta = float(np.pi / 3.0)
    tol = 1e-10

    for n in [8, 12, 16]:
        metrics = _metrics(theta=theta, Nx=n)
        assert metrics["current_l2_rel"] <= tol
