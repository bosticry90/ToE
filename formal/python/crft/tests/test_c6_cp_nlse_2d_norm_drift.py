from __future__ import annotations

import numpy as np

from crft.cp_nlse_2d import CPParams2D, Grid2D, compute_norm_2d, rhs_cp_nlse_2d, simulate_cp_nlse_2d


def test_c6_cp_nlse_2d_norm_drift_is_small_for_plane_wave() -> None:
    # Bounded, deterministic check for the C6 "2D norm preservation" requirement.
    # Use a plane wave with |phi|^2 = rho0 so the nonlinear term cancels even when g_eff != 0.
    Nx = Ny = 24
    Lx = Ly = 2.0 * np.pi
    grid = Grid2D.from_box(Nx=Nx, Ny=Ny, Lx=Lx, Ly=Ly)

    params = CPParams2D(g_eff=9.8696, rho0=1.0)

    kx = 2.0 * np.pi / Lx
    ky = 0.0
    phi0 = np.sqrt(params.rho0) * np.exp(1j * (kx * grid.x + ky * grid.y))

    n0 = compute_norm_2d(phi0, grid)

    dt = 0.01
    n_steps = 250
    phiT = simulate_cp_nlse_2d(
        t0=0.0,
        psi0=phi0,
        dt=dt,
        n_steps=n_steps,
        rhs=rhs_cp_nlse_2d,
        grid=grid,
        params=params,
    )

    nT = compute_norm_2d(phiT, grid)
    drift = abs(nT - n0) / n0

    # Tight but realistic for RK4 on a smooth plane wave.
    assert drift < 1e-8
