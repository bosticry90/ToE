"""CRFT C6 — 2D CP–NLSE plane-wave dispersion test.

This test evolves a 2D plane wave under the CP–NLSE branch
with g = 0 (pure linear Schrödinger) and estimates the
temporal frequency from the time series at a single grid point.

For a plane wave exp(i(kx x + ky y)), the theoretical angular
frequency is

    omega_th = 0.5 * (kx**2 + ky**2)

for the model

    i d_t psi = -0.5 * Laplacian psi.

The test passes if the numerically measured omega agrees with
omega_th within a modest relative tolerance.
"""

import numpy as np
import math

from crft.cp_nlse_2d import (
    Grid2D,
    CPParams2D,
    rhs_cp_nlse_2d,
    simulate_cp_nlse_2d,
)


def estimate_frequency(tvals: np.ndarray, z: np.ndarray) -> float:
    """Estimate dominant angular frequency from a real-valued time series."""
    z = np.real(np.asarray(z))
    zc = z - z.mean()
    Y = np.fft.rfft(zc)
    freqs = np.fft.rfftfreq(len(zc), d=(tvals[1] - tvals[0]))
    # Ignore zero-frequency mode
    idx = 1 + np.argmax(np.abs(Y[1:]))
    omega = 2.0 * math.pi * freqs[idx]
    return omega


def run_crft_c6_cp_nlse_2d_dispersion():
    print("=== CRFT C6 — 2D CP–NLSE Dispersion ===")

    # Grid and parameters chosen to keep the plane wave well resolved.
    Nx = Ny = 32
    Lx = Ly = 2.0 * math.pi
    grid = Grid2D.from_box(Nx=Nx, Ny=Ny, Lx=Lx, Ly=Ly)

    # Linear Schrödinger (no nonlinearity) to isolate dispersion
    params = CPParams2D(g=0.0, rho0=1.0)

    # Fundamental mode in x, zero mode in y
    kx_idx = 1
    ky_idx = 0
    kx = 2.0 * math.pi * kx_idx / Lx
    ky = 0.0

    rho0 = params.rho0
    psi0 = (rho0 ** 0.5) * np.exp(1j * (kx * grid.x + ky * grid.y))

    # Integration parameters: long enough to resolve the frequency
    dt = 0.002
    t0 = 0.0
    t_final = 80.0
    n_steps = int(round((t_final - t0) / dt))

    samples = []
    tvals = []

    def sampler(t, psi):
        tvals.append(t)
        samples.append(psi[0, 0])

    simulate_cp_nlse_2d(
        t0=t0,
        psi0=psi0,
        dt=dt,
        n_steps=n_steps,
        rhs=rhs_cp_nlse_2d,
        grid=grid,
        params=params,
        sample_callback=sampler,
    )

    tvals = np.asarray(tvals)
    samples = np.asarray(samples)

    omega_num = estimate_frequency(tvals, samples)
    omega_th = 0.5 * (kx ** 2 + ky ** 2)
    rel_error = abs(omega_num - omega_th) / omega_th

    print(f"k = ({kx: .6e}, {ky: .6e})")
    print(f"omega_num = {omega_num: .6e}")
    print(f"omega_th  = {omega_th: .6e}")
    print(f"rel_error = {rel_error: .3e}")

    tol = 1.0e-1
    if rel_error < tol:
        print(f"Relative error {rel_error: .3e} < {tol: .1e} : PASS")
    else:
        print(f"Relative error {rel_error: .3e} ≥ {tol: .1e} : FAIL")


if __name__ == "__main__":
    run_crft_c6_cp_nlse_2d_dispersion()
