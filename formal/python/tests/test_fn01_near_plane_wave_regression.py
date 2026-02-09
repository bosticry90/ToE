# formal/python/tests/test_fn01_near_plane_wave_regression.py
#
# FN-01 → DR-01 tightening (Behavioral / Python):
# Extend the DR-01 consequence check beyond exact plane waves to a small
# near-plane-wave wavepacket.
#
# Scope:
# - Deterministic, small-grid, small-time regression.
# - Uses the same narrow omega(k) extraction style as Phase-B solver tests,
#   but with a Gaussian envelope to approximate a finite superposition.
# - No physical claims.

import numpy as np


def _grid(L, N):
    x = np.linspace(0.0, L, N, endpoint=False)
    return x


def _kgrid(L, N):
    dx = L / N
    return 2.0 * np.pi * np.fft.fftfreq(N, d=dx)


def _periodic_dx(x, x0, L):
    d = np.abs(x - x0)
    return np.minimum(d, L - d)


def _wavepacket(A, kx0, ky0, X, Y, *, L, sigma):
    x0 = L / 2.0
    y0 = L / 2.0
    dx = _periodic_dx(X, x0, L)
    dy = _periodic_dx(Y, y0, L)
    env = np.exp(-0.5 * (dx * dx + dy * dy) / (sigma * sigma))
    carrier = np.exp(1j * (kx0 * X + ky0 * Y))
    return (A * env * carrier).astype(np.complex128)


def _mode(X, Y, kx0, ky0):
    return np.exp(-1j * (kx0 * X + ky0 * Y))


def _estimate_omega(times, amps):
    phases = np.unwrap(np.angle(amps))
    slope, _ = np.polyfit(times, phases, deg=1)
    return -slope


def _split_step_solve(
    psi0,
    *,
    L=2.0 * np.pi,
    dt=1e-3,
    nsteps=2000,
    sample_every=40,
    V=0.0,
    g=0.0,
):
    """Minimal 2D spectral split-step for

        i ψ_t = -1/2 Δψ + V ψ + g |ψ|^2 ψ.

    This is intentionally minimal and deterministic.
    """
    N = psi0.shape[0]
    kx = _kgrid(L, N)
    ky = _kgrid(L, N)
    KX, KY = np.meshgrid(kx, ky, indexing="ij")

    Hk = 0.5 * (KX * KX + KY * KY) + V
    linear_prop = np.exp(-1j * dt * Hk)

    psi = psi0.astype(np.complex128, copy=True)

    times = [0.0]
    snaps = [psi.copy()]

    for step in range(1, nsteps + 1):
        if g != 0.0:
            psi *= np.exp(-1j * (g * np.abs(psi) ** 2) * (dt / 2.0))

        psi_hat = np.fft.fftn(psi)
        psi_hat *= linear_prop
        psi = np.fft.ifftn(psi_hat)

        if g != 0.0:
            psi *= np.exp(-1j * (g * np.abs(psi) ** 2) * (dt / 2.0))

        if step % sample_every == 0:
            times.append(step * dt)
            snaps.append(psi.copy())

    return np.array(times), snaps


def _project_mode(psi, basis_mode):
    N = psi.shape[0]
    return (psi * basis_mode).sum() / (N * N)


def test_near_plane_wavepacket_cubic_is_near_unshifted_in_small_amplitude_limit():
    # Choose integer wave numbers on L=2π.
    kx0, ky0 = 2.0, 1.0
    omega0 = 0.5 * (kx0 * kx0 + ky0 * ky0)

    N = 32
    L = 2.0 * np.pi
    x = _grid(L, N)
    y = _grid(L, N)
    X, Y = np.meshgrid(x, y, indexing="ij")

    psi0 = _wavepacket(A=1e-4, kx0=kx0, ky0=ky0, X=X, Y=Y, L=L, sigma=0.7)
    basis = _mode(X, Y, kx0, ky0)

    # Baseline linear evolution.
    t0, snaps0 = _split_step_solve(psi0, L=L, dt=1e-3, nsteps=2000, sample_every=40, V=0.0, g=0.0)
    amps0 = np.array([_project_mode(psi, basis) for psi in snaps0])
    omega_hat0 = _estimate_omega(t0, amps0)

    # FN-style purely nonlinear perturbation. Tiny amplitude => negligible nonlinear shift.
    t1, snaps1 = _split_step_solve(psi0, L=L, dt=1e-3, nsteps=2000, sample_every=40, V=0.0, g=1.0)
    amps1 = np.array([_project_mode(psi, basis) for psi in snaps1])
    omega_hat1 = _estimate_omega(t1, amps1)

    assert abs(omega_hat0 - omega0) < 2e-2
    assert abs(omega_hat1 - omega0) < 2e-2


def test_near_plane_wavepacket_linear_potential_shifts_omega():
    # CT-01-fail family: +V ψ shifts omega by +V even for a wavepacket.
    kx0, ky0 = 2.0, 1.0
    omega0 = 0.5 * (kx0 * kx0 + ky0 * ky0)
    V = 0.4

    N = 32
    L = 2.0 * np.pi
    x = _grid(L, N)
    y = _grid(L, N)
    X, Y = np.meshgrid(x, y, indexing="ij")

    psi0 = _wavepacket(A=1e-4, kx0=kx0, ky0=ky0, X=X, Y=Y, L=L, sigma=0.7)
    basis = _mode(X, Y, kx0, ky0)

    times, snaps = _split_step_solve(psi0, L=L, dt=1e-3, nsteps=2000, sample_every=40, V=V, g=0.0)
    amps = np.array([_project_mode(psi, basis) for psi in snaps])
    omega_hat = _estimate_omega(times, amps)

    assert abs((omega_hat - omega0) - V) < 2e-2
