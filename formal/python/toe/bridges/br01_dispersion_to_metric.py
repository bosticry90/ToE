"""BR-01 (Dispersion → metric mapping) Python front door.

Policy:
- Downstream code MUST import BR-01 only from this module.
- Concrete implementations live in br01_candidates.py and must not be imported
  directly (enforced by tests).

This file intentionally provides a small, stable API surface.
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np

from formal.python.crft import acoustic_metric as mt01
from formal.python.toe.dr01_fit import DR01Fit1D
from formal.python.toe.dr01_fit_curved import DR01FitCurved1D
from formal.python.toe.bridges import br01_candidates as _cands


@dataclass(frozen=True)
class BR01Report:
    max_abs_residual: float
    details: str
    input_fingerprint: str
    input_data_fingerprint: str | None


@dataclass(frozen=True)
class BR01MetricVector1D:
    """Minimal prune-relevant metric surface for BR-01.

    This keeps BR-01 outputs in a deterministic scalar form suitable for locks/tables.
    """

    c_s2: float
    g_tt: float
    g_tx: float
    g_xx: float
    input_fingerprint: str
    input_data_fingerprint: str | None
    source: str


def br01_metric_from_DR01_fit(dr01_fit: DR01Fit1D, *, normalize: bool = True, n: int = 1) -> mt01.AcousticMetric1D:
    """Map a 1D DR-01 fit object to an MT-01 acoustic metric.

    Current canonical gauge: unit density rho ≡ 1, and g_eff = c_s^2.

    Args:
        dr01_fit: Canonical DR-01 fit artifact.
        normalize: Reserved for future gauge/normalization choices.
        n: Length of the 1D grid (creates constant fields).

    Returns:
        AcousticMetric1D with constant component fields.
    """

    _ = normalize
    return _cands.BR01_metric_from_DR01_fit_unit_density(dr01_fit, n=n)


def br01_metric_from_DR01_fit_curved(
    dr01_fit_curved: DR01FitCurved1D,
    *,
    normalize: bool = True,
    n: int = 1,
) -> mt01.AcousticMetric1D:
    """Map a curvature-aware DR fit object to an MT-01 acoustic metric.

    Current policy: BR-01 consumes an effective (u, c_s) pair.
    For the curved model omega/k = c0 + beta*k^2 (with u fixed), we map:

        u_eff  := u
        c_s0   := c0  (k->0 limit)

    Traceability: downstream reports must record the curved-fit fingerprint;
    this function intentionally returns only the metric object.
    """

    _ = normalize

    dr01_linearized = DR01Fit1D(
        u=float(dr01_fit_curved.u),
        c_s=float(dr01_fit_curved.c0),
        tag=f"BR01_linearized_from_curved:{dr01_fit_curved.tag}",
        source_kind="synthetic",
        source_ref=dr01_fit_curved.fingerprint(),
        data_fingerprint=dr01_fit_curved.data_fingerprint,
        fit_method_tag="BR-01 uses c0 as c_s(k->0)",
        sample_kw=None,
    )

    return _cands.BR01_metric_from_DR01_fit_unit_density(dr01_linearized, n=n)


def br01_metric_from_DR01(dr01: DR01Fit1D, *, normalize: bool = True, n: int = 1) -> mt01.AcousticMetric1D:
    """Backward-compatible alias of br01_metric_from_DR01_fit."""

    return br01_metric_from_DR01_fit(dr01, normalize=normalize, n=n)


def br01_metric_vector_from_DR01_fit(
    dr01_fit: DR01Fit1D,
    *,
    normalize: bool = True,
) -> BR01MetricVector1D:
    """Front-door scalar metric vector for a DR-01 linear fit artifact."""
    if not isinstance(dr01_fit, DR01Fit1D):
        raise TypeError("br01_metric_vector_from_DR01_fit requires DR01Fit1D input")

    metric = br01_metric_from_DR01_fit(dr01_fit, normalize=normalize, n=1)
    return BR01MetricVector1D(
        c_s2=float(np.asarray(metric.c_s2).ravel()[0]),
        g_tt=float(np.asarray(metric.g_tt).ravel()[0]),
        g_tx=float(np.asarray(metric.g_tx).ravel()[0]),
        g_xx=float(np.asarray(metric.g_xx).ravel()[0]),
        input_fingerprint=dr01_fit.fingerprint(),
        input_data_fingerprint=dr01_fit.data_fingerprint,
        source="DR01Fit1D",
    )


def br01_metric_vector_from_DR01_fit_curved(
    dr01_fit_curved: DR01FitCurved1D,
    *,
    normalize: bool = True,
) -> BR01MetricVector1D:
    """Front-door scalar metric vector for a DR-01 curved fit artifact."""
    if not isinstance(dr01_fit_curved, DR01FitCurved1D):
        raise TypeError("br01_metric_vector_from_DR01_fit_curved requires DR01FitCurved1D input")

    metric = br01_metric_from_DR01_fit_curved(dr01_fit_curved, normalize=normalize, n=1)
    return BR01MetricVector1D(
        c_s2=float(np.asarray(metric.c_s2).ravel()[0]),
        g_tt=float(np.asarray(metric.g_tt).ravel()[0]),
        g_tx=float(np.asarray(metric.g_tx).ravel()[0]),
        g_xx=float(np.asarray(metric.g_xx).ravel()[0]),
        input_fingerprint=dr01_fit_curved.fingerprint(),
        input_data_fingerprint=dr01_fit_curved.data_fingerprint,
        source="DR01FitCurved1D",
    )


def _extract_u_cs2_from_metric_1d(metric: mt01.AcousticMetric1D) -> tuple[float, float]:
    # For the MT-01 construction:
    #   g_tx = -u
    #   g_tt = -(c_s2 - u^2) = -c_s2 + u^2
    # so c_s2 = u^2 - g_tt.
    g_tx0 = float(np.asarray(metric.g_tx).ravel()[0])
    g_tt0 = float(np.asarray(metric.g_tt).ravel()[0])
    u = -g_tx0
    cs2 = u * u - g_tt0
    return u, cs2


def br01_predict_omega_from_metric_1d(metric: mt01.AcousticMetric1D, k: float) -> float:
    """Predict ω(k) from a 1D acoustic metric using the + branch.

    Uses ω(k) = u*k + sqrt(c_s2)*|k|.
    """

    u, cs2 = _extract_u_cs2_from_metric_1d(metric)
    cs = float(np.sqrt(max(0.0, cs2)))
    return float(u * k + cs * abs(k))


def br01_check_consistency(dr01_fit: DR01Fit1D, metric: mt01.AcousticMetric1D, *, tol: float = 1e-12) -> BR01Report:
    """Consistency check: metric-implied (u, c_s) matches the DR-01 fit artifact."""

    u_hat, cs2_hat = _extract_u_cs2_from_metric_1d(metric)
    cs_hat = float(np.sqrt(max(0.0, cs2_hat)))

    du = abs(u_hat - float(dr01_fit.u))
    dcs = abs(cs_hat - float(dr01_fit.c_s))
    max_abs = max(du, dcs)

    ok = max_abs <= tol
    details = (
        f"u_hat={u_hat:.16g} u={float(dr01_fit.u):.16g} du={du:.3g}; "
        f"c_s_hat={cs_hat:.16g} c_s={float(dr01_fit.c_s):.16g} dcs={dcs:.3g}; "
        f"tol={tol:.3g}; ok={ok}"
    )

    return BR01Report(
        max_abs_residual=max_abs,
        details=details,
        input_fingerprint=dr01_fit.fingerprint(),
        input_data_fingerprint=dr01_fit.data_fingerprint,
    )
