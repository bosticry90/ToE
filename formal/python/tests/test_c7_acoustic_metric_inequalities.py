from __future__ import annotations

import numpy as np

from formal.python.crft import acoustic_metric as mt01


def test_c7_acoustic_metric_1d_has_timelike_gtt_and_negative_det_when_subsonic() -> None:
    rho = np.full(64, 2.0)
    u = np.full(64, 0.1)
    g_eff = 1.25

    m = mt01.compute_acoustic_metric_1d(rho=rho, u=u, g_eff=g_eff)
    det = mt01.metric_determinant_1d(m)

    # For subsonic flow u^2 < c_s^2 = g_eff * rho, we expect g_tt < 0.
    assert np.all(m.g_tt < 0.0)
    # With g_xx = 1 and g_tx = -u, det reduces to -c_s^2, hence negative for rho > 0, g_eff > 0.
    assert np.all(det < 0.0)


def test_c7_acoustic_metric_2d_has_timelike_gtt_and_negative_det_when_subsonic() -> None:
    rho = np.full((12, 10), 1.7)
    u_x = np.full((12, 10), 0.05)
    u_y = np.full((12, 10), 0.03)
    g_eff = 0.9

    m = mt01.compute_acoustic_metric_2d(rho=rho, u_x=u_x, u_y=u_y, g_eff=g_eff)
    det = mt01.metric_determinant_2d(m)

    assert np.all(m.g_tt < 0.0)
    assert np.all(det < 0.0)
