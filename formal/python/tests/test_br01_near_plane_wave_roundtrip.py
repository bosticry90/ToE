import numpy as np

from formal.python.toe.bridges.br01_dispersion_to_metric import (
    DR01Fit1D,
    br01_metric_from_DR01_fit,
    br01_check_consistency,
    br01_predict_omega_from_metric_1d,
)


def _estimate_omega_from_wavepacket(x: np.ndarray, psi0: np.ndarray, psi1: np.ndarray, dt: float) -> float:
    # Project onto the initial wavepacket and read phase advance.
    z0 = np.vdot(psi0, psi0)
    z1 = np.vdot(psi0, psi1)
    phase = np.angle(z1 / z0)
    return float(-phase / dt)


def test_br01_near_plane_wave_roundtrip_via_wavepacket_phase():
    # Deterministic near-plane-wave “behavioral lock”: a Gaussian-enveloped plane wave
    # with analytic time dependence is used to estimate ω(k) via projection phase.
    # BR-01 must map the implied DR-01 object to a metric that reproduces ω(k).

    n = 512
    L = 50.0
    x = np.linspace(-L / 2, L / 2, n, endpoint=False)

    k0 = 0.9
    u = 0.15
    c_s = 1.2
    sample_ks = (-3.0, -2.0, -1.0, -0.5, 0.5, 1.0, 2.0, 3.0)
    sample_kw = tuple((k, u * k + c_s * abs(k)) for k in sample_ks)
    dr01 = DR01Fit1D(
        u=u,
        c_s=c_s,
        tag="wavepacket",
        source_kind="synthetic",
        source_ref="br01_near_plane_wave_roundtrip",
        fit_method_tag="analytic_v1",
        sample_kw=sample_kw,
    )
    assert dr01.data_fingerprint is not None
    assert dr01.source_kind != "unknown"

    omega = dr01.omega(k0)
    sigma = 6.0
    envelope = np.exp(-(x**2) / (2 * sigma**2))

    t0 = 0.0
    t1 = 0.35
    dt = t1 - t0

    psi0 = envelope * np.exp(1j * (k0 * x - omega * t0))
    psi1 = envelope * np.exp(1j * (k0 * x - omega * t1))

    omega_hat = _estimate_omega_from_wavepacket(x, psi0, psi1, dt)

    metric = br01_metric_from_DR01_fit(dr01, n=1)
    omega_pred = br01_predict_omega_from_metric_1d(metric, k0)
    rep = br01_check_consistency(dr01, metric, tol=1e-12)
    assert rep.input_data_fingerprint == dr01.data_fingerprint

    assert abs(omega_hat - omega) < 5e-12
    assert abs(omega_pred - omega) < 5e-12
