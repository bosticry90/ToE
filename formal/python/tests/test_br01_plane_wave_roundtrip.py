import numpy as np

from formal.python.toe.bridges.br01_dispersion_to_metric import (
    DR01Fit1D,
    br01_check_consistency,
    br01_metric_from_DR01_fit,
    br01_predict_omega_from_metric_1d,
)


def test_br01_plane_wave_roundtrip_matches_dr01_surrogate():
    rng = np.random.default_rng(0)

    u = float(rng.uniform(-0.4, 0.4))
    c_s = float(rng.uniform(0.2, 2.0))

    sample_ks = (-3.0, -2.0, -1.0, -0.5, 0.5, 1.0, 2.0, 3.0)
    sample_kw = tuple((k, u * k + c_s * abs(k)) for k in sample_ks)
    dr01 = DR01Fit1D(
        u=u,
        c_s=c_s,
        tag="plane-wave",
        source_kind="synthetic",
        source_ref="br01_plane_wave_roundtrip",
        fit_method_tag="analytic_v1",
        sample_kw=sample_kw,
    )
    assert dr01.data_fingerprint is not None
    assert dr01.source_kind != "unknown"

    metric = br01_metric_from_DR01_fit(dr01, n=3)
    rep = br01_check_consistency(dr01, metric, tol=1e-12)
    assert rep.max_abs_residual <= 1e-12, rep.details
    assert rep.input_fingerprint == dr01.fingerprint()
    assert rep.input_data_fingerprint == dr01.data_fingerprint

    ks = np.linspace(-3.0, 3.0, 31)
    for k in ks:
        w_dr = dr01.omega(float(k))
        w_m = br01_predict_omega_from_metric_1d(metric, float(k))
        assert abs(w_dr - w_m) < 1e-12
