import numpy as np
import pytest

def mk_grid(N=64, L=2*np.pi):
    x = np.linspace(0, L, N, endpoint=False)
    X, Y = np.meshgrid(x, x, indexing="ij")
    k = 2*np.pi*np.fft.fftfreq(N, d=L/N)
    KX, KY = np.meshgrid(k, k, indexing="ij")
    return X, Y, KX, KY

def dxx(psi, KX):
    phat = np.fft.fft2(psi)
    return np.fft.ifft2(-(KX**2) * phat)

def dyy(psi, KY):
    phat = np.fft.fft2(psi)
    return np.fft.ifft2(-(KY**2) * phat)

def lap(psi, KX, KY):
    phat = np.fft.fft2(psi)
    return np.fft.ifft2(-((KX**2 + KY**2)) * phat)

def rand_field(N, seed=0):
    rng = np.random.default_rng(seed)
    a = rng.normal(size=(N, N))
    b = rng.normal(size=(N, N))
    return (a + 1j*b).astype(np.complex128)

# Deformation representatives P[ψ]
def P_cubic(psi, **kw):
    g = kw.get("g", 0.3)
    return g * (np.abs(psi)**2) * psi

def P_conj(psi, **kw):
    return np.conj(psi)

def P_xpsi(psi, **kw):
    X = kw["X"]
    return X * psi

def P_lap(psi, **kw):
    return lap(psi, kw["KX"], kw["KY"])

def P_dxx(psi, **kw):
    return dxx(psi, kw["KX"])

def P_dxx_minus_dyy(psi, **kw):
    return dxx(psi, kw["KX"]) - dyy(psi, kw["KY"])

CASES = [
    ("cubic", P_cubic, True,  True,  True),
    ("conj",  P_conj,  False, True,  True),
    ("xpsi",  P_xpsi,  True,  False, False),
    ("lap",   P_lap,   True,  True,  True),
    ("dxx",   P_dxx,   True,  True,  False),
    ("dxx-dyy", P_dxx_minus_dyy, True, True, False),
]

def close(a, b, rtol=1e-9, atol=1e-9):
    return np.allclose(a, b, rtol=rtol, atol=atol)

@pytest.mark.parametrize("name,P,exp_phase,exp_shift,exp_rot", CASES)
def test_sym01_phase_invariance(name, P, exp_phase, exp_shift, exp_rot):
    N = 64
    X, Y, KX, KY = mk_grid(N)
    psi = rand_field(N, seed=1)

    thetas = [0.1, 0.7, 1.3]
    ok = True
    for th in thetas:
        lhs = P(np.exp(1j*th)*psi, X=X, Y=Y, KX=KX, KY=KY)
        rhs = np.exp(1j*th) * P(psi, X=X, Y=Y, KX=KX, KY=KY)
        ok = ok and close(lhs, rhs, rtol=1e-7, atol=1e-7)
    assert ok == exp_phase, f"{name}: phase invariance expected {exp_phase}"

@pytest.mark.parametrize("name,P,exp_phase,exp_shift,exp_rot", CASES)
def test_sym01_translation_invariance(name, P, exp_phase, exp_shift, exp_rot):
    N = 64
    X, Y, KX, KY = mk_grid(N)
    psi = rand_field(N, seed=2)

    shifts = [(1,0), (0,3), (5,7)]
    ok = True
    for sx, sy in shifts:
        psi_s = np.roll(np.roll(psi, sx, axis=0), sy, axis=1)
        lhs = P(psi_s, X=X, Y=Y, KX=KX, KY=KY)
        rhs = np.roll(np.roll(P(psi, X=X, Y=Y, KX=KX, KY=KY), sx, axis=0), sy, axis=1)
        ok = ok and close(lhs, rhs, rtol=1e-7, atol=1e-7)
    assert ok == exp_shift, f"{name}: translation invariance expected {exp_shift}"

@pytest.mark.parametrize("name,P,exp_phase,exp_shift,exp_rot", CASES)
def test_sym01_rotation_invariance(name, P, exp_phase, exp_shift, exp_rot):
    N = 64
    X, Y, KX, KY = mk_grid(N)
    psi = rand_field(N, seed=3)

    ok = True
    for k in [1,2,3]:
        psi_r = np.rot90(psi, k=k)

        # IMPORTANT: keep grids FIXED for invariance checks.
        lhs = P(psi_r, X=X, Y=Y, KX=KX, KY=KY)
        rhs = np.rot90(P(psi, X=X, Y=Y, KX=KX, KY=KY), k=k)

        ok = ok and close(lhs, rhs, rtol=1e-7, atol=1e-7)

    assert ok == exp_rot, f"{name}: rotation invariance expected {exp_rot}"

