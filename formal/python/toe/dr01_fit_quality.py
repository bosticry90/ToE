"""DR-01 fit-quality diagnostics (deterministic, evidence-friendly).

This module provides minimal, deterministic fit-quality metadata for DR-01
through-origin low-k linearizations of the form:

    omega(k) ~= c_s * k   (forced through origin)

Key design constraints:
- No filesystem I/O.
- Deterministic outputs (suitable for artifact stamping and lock tests).
- Uses only the already-frozen `sample_kw` payload.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import math
from typing import Iterable


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


@dataclass(frozen=True)
class DR01FitQuality1D:
    """Fit-quality diagnostics for a through-origin omega ~= c_s*k fit."""

    n_points: int
    rmse_omega_rad_s: float
    slope_stderr_m_per_s: float
    r2_through_origin: float

    def fingerprint(self) -> str:
        payload = {
            "n_points": int(self.n_points),
            "rmse_omega_rad_s": float(self.rmse_omega_rad_s),
            "slope_stderr_m_per_s": float(self.slope_stderr_m_per_s),
            "r2_through_origin": float(self.r2_through_origin),
        }
        return _sha256_json(payload)


def dr01_quality_through_origin_from_sample_kw(
    sample_kw: Iterable[tuple[float, float]],
) -> DR01FitQuality1D:
    """Compute deterministic fit-quality metrics from a frozen (k, omega) sample.

    Parameters
    ----------
    sample_kw:
        Iterable of (k, omega) pairs with k in m^-1 and omega in rad/s.

    Returns
    -------
    DR01FitQuality1D
        n_points, RMSE of omega residuals, slope standard error (interpretable as
        c_s standard error for this model), and an origin-based R^2 variant.

    Notes
    -----
    - Model is forced through origin with a single parameter (slope = c_s).
    - Standard error uses sigma^2 = SSE/(n-1) for a 1-parameter model.
    - R^2 is defined relative to the y=0 baseline (SST0 = sum(y^2)):
        R^2 = 1 - SSE/SST0
      This is a common choice for through-origin regressions.
    """

    xs: list[float] = []
    ys: list[float] = []
    for k, w in sample_kw:
        xs.append(float(k))
        ys.append(float(w))

    n = len(xs)
    if n < 2:
        raise ValueError("Need at least 2 points to compute fit quality")

    sxx = sum(x * x for x in xs)
    if sxx == 0.0:
        raise ValueError("Degenerate sample: sum(k^2) == 0")

    sxy = sum(x * y for x, y in zip(xs, ys))
    slope = sxy / sxx

    resid = [y - slope * x for x, y in zip(xs, ys)]
    sse = sum(r * r for r in resid)

    rmse = math.sqrt(sse / n)

    # Through-origin: 1 parameter, so dof = n - 1.
    sigma2 = sse / (n - 1)
    slope_stderr = math.sqrt(sigma2 / sxx)

    sst0 = sum(y * y for y in ys)
    r2 = 1.0 - (sse / sst0) if sst0 > 0.0 else float("nan")

    return DR01FitQuality1D(
        n_points=int(n),
        rmse_omega_rad_s=float(rmse),
        slope_stderr_m_per_s=float(slope_stderr),
        r2_through_origin=float(r2),
    )


@dataclass(frozen=True)
class DR01FitQualityCurved1D:
    """Fit-quality diagnostics for omega/k = c0 + beta*k^2 (OLS in y-space)."""

    n_points: int
    rmse_omega_over_k_m_per_s: float
    c0_stderr_m_per_s: float
    beta_stderr_s_per_m2: float
    r2_y_space: float

    def fingerprint(self) -> str:
        payload = {
            "n_points": int(self.n_points),
            "rmse_omega_over_k_m_per_s": float(self.rmse_omega_over_k_m_per_s),
            "c0_stderr_m_per_s": float(self.c0_stderr_m_per_s),
            "beta_stderr_s_per_m2": float(self.beta_stderr_s_per_m2),
            "r2_y_space": float(self.r2_y_space),
        }
        return _sha256_json(payload)


def dr01_quality_curved_from_sample_kw(
    sample_kw: Iterable[tuple[float, float]],
) -> DR01FitQualityCurved1D:
    """Compute deterministic fit-quality metrics for omega/k vs k^2.

    y_i = omega_i / k_i
    x_i = k_i^2
    Fit y = c0 + beta*x by OLS.

    Returns RMSE in y-space and standard errors for (c0, beta).
    """

    items = [(float(k), float(w)) for (k, w) in sample_kw]
    n = len(items)
    if n < 3:
        raise ValueError("Need at least 3 points for curved fit-quality (dof = n-2)")

    ks = [k for (k, _) in items]
    ws = [w for (_, w) in items]

    ys = [w / k for (k, w) in zip(ks, ws)]
    xs = [k * k for k in ks]

    xbar = sum(xs) / n
    ybar = sum(ys) / n

    sxx = sum((x - xbar) * (x - xbar) for x in xs)
    if sxx == 0.0:
        raise ValueError("Degenerate sample: var(k^2) == 0")

    sxy = sum((x - xbar) * (y - ybar) for (x, y) in zip(xs, ys))
    beta = sxy / sxx
    c0 = ybar - beta * xbar

    resid = [y - (c0 + beta * x) for (x, y) in zip(xs, ys)]
    sse = sum(r * r for r in resid)

    rmse = math.sqrt(sse / n)

    # Standard errors via sigma^2 = SSE/(n-2)
    sigma2 = sse / (n - 2)
    beta_stderr = math.sqrt(sigma2 / sxx)
    c0_stderr = math.sqrt(sigma2 * (1.0 / n + (xbar * xbar) / sxx))

    sst = sum((y - ybar) * (y - ybar) for y in ys)
    r2 = 1.0 - (sse / sst) if sst > 0.0 else float("nan")

    return DR01FitQualityCurved1D(
        n_points=int(n),
        rmse_omega_over_k_m_per_s=float(rmse),
        c0_stderr_m_per_s=float(c0_stderr),
        beta_stderr_s_per_m2=float(beta_stderr),
        r2_y_space=float(r2),
    )
