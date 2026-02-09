from __future__ import annotations

import numpy as np

from crft.cp_nlse_2d import CPParams2D, Grid2D, rhs_cp_nlse_2d


def test_c6_cp_nlse_2d_plane_wave_is_rhs_eigenfunction_when_linear() -> None:
    # Bounded dispersion/eigenfunction check:
    # For g_eff=0, rhs should satisfy phi_t = -i * omega * phi for a plane wave,
    # with omega = 0.5 * |k|^2 under the spectral Laplacian.
    Nx = Ny = 16
    Lx = Ly = 2.0 * np.pi
    grid = Grid2D.from_box(Nx=Nx, Ny=Ny, Lx=Lx, Ly=Ly)

    params = CPParams2D(g_eff=0.0, rho0=1.0)

    kx_idx = 1
    ky_idx = 2
    kx = 2.0 * np.pi * kx_idx / Lx
    ky = 2.0 * np.pi * ky_idx / Ly
    omega_th = 0.5 * (kx * kx + ky * ky)

    phi = np.sqrt(params.rho0) * np.exp(1j * (kx * grid.x + ky * grid.y))
    rhs = rhs_cp_nlse_2d(phi, grid, params)

    # Expected: phi_t = -i*omega*phi (since i phi_t = +omega phi).
    expected = -1j * omega_th * phi

    # Use a relative norm tolerance (the spectral Laplacian should be very accurate here).
    err = np.linalg.norm(rhs - expected) / np.linalg.norm(expected)
    assert err < 1e-10
