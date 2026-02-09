"""FN-01 metric-sensitive discriminators.

This module defines minimal, deterministic discriminators that *must* depend on
BR-01/MT-01 outputs. It intentionally contains no filesystem I/O.
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np

from formal.python.toe.bridges.br01_dispersion_to_metric import br01_metric_from_DR01_fit
from formal.python.toe.constraints.fn01_artifact import FN01Artifact1D
from formal.python.toe.dr01_fit import DR01Fit1D


@dataclass(frozen=True)
class FN01CrossFitMetricResidualReport:
    """Report object for FN-01 cross-fit metric stability residual."""

    fn_fingerprint: str
    dr02_fingerprint: str
    dr03_fingerprint: str

    g_tt_02: float
    g_tt_03: float

    epsilon: float
    r_metric: float

    w_fn: float
    score: float


def _first_scalar(x: np.ndarray) -> float:
    return float(np.asarray(x).ravel()[0])


def fn01_cross_fit_metric_residual(
    fn_artifact: FN01Artifact1D,
    dr02_fit: DR01Fit1D,
    dr03_fit: DR01Fit1D,
    *,
    epsilon: float = 1.0e-12,
    w_fn: float = 1.0,
) -> FN01CrossFitMetricResidualReport:
    """Compute a scalar residual that must change when BR-01 output changes.

    Definition:
        r_metric = |g_tt(dr02) - g_tt(dr03)| / max(|g_tt(dr02)|, |g_tt(dr03)|, epsilon)

    Note:
        The current BR-01 gauge makes g_tt tightly linked to c_s^2 (and u), so
        this is equivalent to a normalized c_s^2 drift under the current locks.

    Args:
        fn_artifact: Promoted FN artifact (threaded for lineage; no weighting yet).
        dr02_fit: First DR-01 fit artifact (e.g. DR-02a).
        dr03_fit: Second DR-01 fit artifact (e.g. DR-03a).
        epsilon: Numerical floor for denominator.
        w_fn: FN weight factor (MVP default 1.0).

    Returns:
        FN01CrossFitMetricResidualReport with fingerprints and scalar values.
    """

    if epsilon <= 0.0:
        raise ValueError("epsilon must be positive")

    metric_02 = br01_metric_from_DR01_fit(dr02_fit, n=1)
    metric_03 = br01_metric_from_DR01_fit(dr03_fit, n=1)

    g_tt_02 = _first_scalar(metric_02.g_tt)
    g_tt_03 = _first_scalar(metric_03.g_tt)

    denom = max(abs(g_tt_02), abs(g_tt_03), float(epsilon))
    r_metric = abs(g_tt_02 - g_tt_03) / denom

    score = float(r_metric * float(w_fn))

    return FN01CrossFitMetricResidualReport(
        fn_fingerprint=fn_artifact.fingerprint(),
        dr02_fingerprint=dr02_fit.fingerprint(),
        dr03_fingerprint=dr03_fit.fingerprint(),
        g_tt_02=float(g_tt_02),
        g_tt_03=float(g_tt_03),
        epsilon=float(epsilon),
        r_metric=float(r_metric),
        w_fn=float(w_fn),
        score=score,
    )
