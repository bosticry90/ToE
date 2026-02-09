import numpy as np

def plane_wave(A, kx, ky, omega, x, y, t):
    return A * np.exp(1j * (kx*x + ky*y - omega*t))

def coeff_base(kx, ky):
    return 0.5*(kx*kx + ky*ky)

def test_linear_potential_breaks_dr01():
    rng = np.random.default_rng(0)
    A = rng.normal() + 1j*rng.normal()
    kx = float(rng.uniform(-3, 3))
    ky = float(rng.uniform(-3, 3))
    V = 1.234  # linear potential term V ψ

    # If equation is i∂t ψ = -(1/2)Δψ + V ψ,
    # then coefficient identity becomes ω = (kx^2+ky^2)/2 + V
    omega = coeff_base(kx, ky)  # DR-01 candidate (unchanged)

    x = float(rng.uniform(-1, 1))
    y = float(rng.uniform(-1, 1))
    t = float(rng.uniform(-1, 1))
    psi = plane_wave(A, kx, ky, omega, x, y, t)

    lhs = omega * psi
    rhs = (coeff_base(kx, ky) + V) * psi

    # Must fail if V != 0
    with np.testing.assert_raises(AssertionError):
        np.testing.assert_allclose(lhs, rhs, rtol=0, atol=1e-12)

def test_cubic_term_preserves_dr01_under_linearization():
    rng = np.random.default_rng(1)
    A = rng.normal() + 1j*rng.normal()
    kx = float(rng.uniform(-3, 3))
    ky = float(rng.uniform(-3, 3))

    omega = coeff_base(kx, ky)

    x = float(rng.uniform(-1, 1))
    y = float(rng.uniform(-1, 1))
    t = float(rng.uniform(-1, 1))
    psi = plane_wave(A, kx, ky, omega, x, y, t)

    # cubic term g|ψ|^2 ψ is nonlinear; linearization about ψ=0 contributes 0
    # so the coefficient identity remains ω ψ = (kx^2+ky^2)/2 ψ
    lhs = omega * psi
    rhs = coeff_base(kx, ky) * psi
    np.testing.assert_allclose(lhs, rhs, rtol=0, atol=1e-12)
