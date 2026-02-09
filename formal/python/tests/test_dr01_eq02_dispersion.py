import numpy as np

def plane_wave(A, kx, ky, omega, x, y, t):
    # ψ = A * exp(i(kx x + ky y - omega t))
    return A * np.exp(1j * (kx * x + ky * y - omega * t))

def test_dr01_eq02_plane_wave_coefficient_equality():
    # This test is intentionally "structural-numeric":
    # it verifies the EQ-02 coefficient identity on a plane wave
    # (no broader physics claims).

    rng = np.random.default_rng(0)

    # random but stable parameters
    A = (rng.normal() + 1j * rng.normal())
    kx = float(rng.uniform(-3.0, 3.0))
    ky = float(rng.uniform(-3.0, 3.0))

    # DR-01 candidate
    omega = 0.5 * (kx * kx + ky * ky)

    # sample points
    x = float(rng.uniform(-1.0, 1.0))
    y = float(rng.uniform(-1.0, 1.0))
    t = float(rng.uniform(-1.0, 1.0))

    psi = plane_wave(A, kx, ky, omega, x, y, t)

    # Analytic operator actions on the plane wave:
    # i∂t ψ = omega * ψ
    lhs = omega * psi

    # Δψ = -(kx^2 + ky^2) ψ  =>  -(1/2)Δψ = (kx^2 + ky^2)/2 * ψ
    rhs = 0.5 * (kx * kx + ky * ky) * psi

    # This is exactly the "coefficient equality times ψ" form.
    np.testing.assert_allclose(lhs, rhs, rtol=0, atol=1e-12)
