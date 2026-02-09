from formal.python.toe.dr01_fit import DR01Fit1D


def test_dr01_fit_artifact_provenance_is_stamped_and_deterministic():
    u = 0.12
    c_s = 1.34

    sample_ks = (-3.0, -2.0, -1.0, -0.5, 0.5, 1.0, 2.0, 3.0)
    sample_kw = tuple((k, u * k + c_s * abs(k)) for k in sample_ks)

    dr01 = DR01Fit1D(
        u=u,
        c_s=c_s,
        tag="provenance-test",
        source_kind="synthetic",
        source_ref="test_dr01_fit_artifact_provenance",
        fit_method_tag="analytic_v1",
        sample_kw=sample_kw,
    )

    assert dr01.source_kind != "unknown"
    assert dr01.data_fingerprint is not None

    fp1 = dr01.fingerprint()
    fp2 = dr01.fingerprint()
    assert fp1 == fp2

    # If the underlying data changes, the data_fingerprint must change.
    sample_kw_2 = sample_kw[:-1] + ((4.0, u * 4.0 + c_s * abs(4.0)),)
    dr01_2 = DR01Fit1D(
        u=u,
        c_s=c_s,
        tag="provenance-test",
        source_kind="synthetic",
        source_ref="test_dr01_fit_artifact_provenance",
        fit_method_tag="analytic_v1",
        sample_kw=sample_kw_2,
    )

    assert dr01_2.data_fingerprint is not None
    assert dr01_2.data_fingerprint != dr01.data_fingerprint
