# Pinned legacy reference (verbatim copy)
# Source: scratch/quarantine/20260118/archive/tests/test_phase51_coherence_drift_metrics.py
# Note: This file is stored for traceability only; it is not imported/executed by OV-UCFF-02.

import numpy as np

from equations.phase51_coherence_drift_metrics import (
    roughness_drift,
    spectrum_shift,
    correlation_length_drift,
    coherence_drift_report,
)
from equations.phase50_coherence_metrics import structure_factor


def _plane_wave_1d(n=256, L=40.0, k0=1.7):
    x = np.linspace(-L / 2, L / 2, n, endpoint=False)
    dx = x[1] - x[0]
    psi = np.exp(1j * k0 * x)
    return x, dx, psi


def _noisy_field_1d(n=256, L=40.0, seed=0, amp=0.3):
    x = np.linspace(-L / 2, L / 2, n, endpoint=False)
    dx = x[1] - x[0]
    rng = np.random.default_rng(seed)
    noise = amp * (rng.standard_normal(n) + 1j * rng.standard_normal(n))
    psi = 1.0 + noise
    return x, dx, psi


def test_roughness_drift_plane_wave_near_zero():
    _, dx, psi = _plane_wave_1d()
    out = roughness_drift(psi, psi, dx=dx, kind="density")
    assert abs(out["drift"]) < 1e-3
    assert abs(out["ratio"] - 1.0) < 1e-3


def test_roughness_drift_plane_to_noise_positive():
    _, dx, psi_pw = _plane_wave_1d()
    _, _, psi_n = _noisy_field_1d(seed=10, amp=0.35)

    out = roughness_drift(psi_pw, psi_n, dx=dx, kind="density")
    assert out["roughnessT"] > out["roughness0"]
    assert out["drift"] > 0.0


def test_correlation_length_drift_orders_plane_vs_noise():
    _, dx, psi_pw = _plane_wave_1d()
    _, _, psi_n = _noisy_field_1d(seed=123, amp=0.3)

    out = correlation_length_drift(psi_pw, psi_n, dx=dx, max_lag=80, normalize=True)
    # coherence length should drop going to noise
    assert out["xi0"] > out["xiT"]
    assert out["ratio"] < 1.0


def test_spectrum_shift_zero_for_identical_fields():
    _, dx, psi = _plane_wave_1d()
    S0 = structure_factor(psi, dx=dx, detrend_mean=True)
    ST = structure_factor(psi, dx=dx, detrend_mean=True)
    k = 2 * np.pi * np.fft.fftfreq(len(psi), d=dx)

    out = spectrum_shift(S0, ST, k=k, method="centroid")
    assert abs(out["shift"]) < 1e-8
    assert abs(out["ratio"] - 1.0) < 1e-8


def test_coherence_drift_report_has_keys():
    _, dx, psi_pw = _plane_wave_1d()
    _, _, psi_n = _noisy_field_1d(seed=7, amp=0.25)

    rep = coherence_drift_report(psi_pw, psi_n, dx=dx, max_lag=60)
    assert "roughness_density" in rep
    assert "roughness_field" in rep
    assert "correlation_length" in rep
    assert "spectrum_centroid" in rep


def test_2d_smoke_shapes_and_nonnegativity():
    nx, ny = 64, 64
    psi2 = np.ones((nx, ny), dtype=complex)
    dx = (0.5, 0.5)

    # roughness drift should accept 2D, and be ~ zero for identical fields
    out_r = roughness_drift(psi2, psi2, dx=dx, kind="density")
    assert abs(out_r["drift"]) < 1e-6

    # correlation drift reduces to 1D internally
    out_xi = correlation_length_drift(psi2, psi2, dx=dx, max_lag=20, axis=0)
    assert abs(out_xi["drift"]) < 1e-6
