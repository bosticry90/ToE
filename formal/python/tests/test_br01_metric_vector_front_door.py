from __future__ import annotations

from formal.python.toe.bridges.br01_dispersion_to_metric import (
    BR01MetricVector1D,
    br01_metric_vector_from_DR01_fit,
    br01_metric_vector_from_DR01_fit_curved,
)
from formal.python.toe.dr01_fit import DR01Fit1D
from formal.python.toe.dr01_fit_curved import dr01_fit_curved_from_sample_kw


def test_br01_metric_vector_from_linear_fit_is_deterministic():
    sample_kw = (
        (1.0, 1.3),
        (2.0, 2.6),
        (3.0, 3.9),
    )
    fit = DR01Fit1D(
        u=0.0,
        c_s=1.3,
        tag="dr01-linear-test",
        source_kind="synthetic",
        source_ref="pytest",
        fit_method_tag="analytic",
        sample_kw=sample_kw,
    )

    v1 = br01_metric_vector_from_DR01_fit(fit)
    v2 = br01_metric_vector_from_DR01_fit(fit)
    assert isinstance(v1, BR01MetricVector1D)
    assert v1 == v2
    assert abs(v1.c_s2 - (fit.c_s**2)) < 1e-12
    assert abs(v1.g_tx - (-fit.u)) < 1e-12
    assert v1.source == "DR01Fit1D"
    assert v1.input_data_fingerprint == fit.data_fingerprint


def test_br01_metric_vector_from_curved_fit_is_deterministic():
    sample_kw = (
        (1.0, 1.2),
        (2.0, 2.6),
        (3.0, 4.5),
        (4.0, 7.0),
    )
    fit = dr01_fit_curved_from_sample_kw(
        sample_kw,
        u_fixed=0.0,
        tag="dr01-curved-test",
        source_kind="synthetic",
        source_ref="pytest",
        fit_method_tag="curved",
    )

    v1 = br01_metric_vector_from_DR01_fit_curved(fit)
    v2 = br01_metric_vector_from_DR01_fit_curved(fit)
    assert isinstance(v1, BR01MetricVector1D)
    assert v1 == v2
    assert abs(v1.c_s2 - (fit.c0**2)) < 1e-12
    assert v1.source == "DR01FitCurved1D"
    assert v1.input_data_fingerprint == fit.data_fingerprint


def test_br01_metric_vector_front_door_rejects_non_artifact_input():
    try:
        br01_metric_vector_from_DR01_fit({"u": 0.0, "c_s": 1.0})  # type: ignore[arg-type]
        raised = False
    except TypeError:
        raised = True
    assert raised

    try:
        br01_metric_vector_from_DR01_fit_curved({"u": 0.0, "c0": 1.0, "beta": 0.0})  # type: ignore[arg-type]
        raised_curved = False
    except TypeError:
        raised_curved = True
    assert raised_curved
