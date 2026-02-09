"""Curvature-aware DR-01 fit artifacts (public surface).

This module defines a second, minimal *fit object* type intended to test whether
strict through-origin linearization is too rigid in the low-k band.

Model (with u fixed, default 0):

    omega(k) / k = c0 + beta * k^2

Equivalently (for k >= 0):

    omega(k) = u*k + c0*k + beta*k^3

Design constraints:
- Deterministic (no RNG).
- No filesystem I/O.
- Carries the same provenance + data_fingerprint discipline as DR01Fit1D.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import math
from typing import Iterable, Literal

from formal.python.toe.dr01_fit import DR01Fit1D
from formal.python.toe.dr01_fit_quality import DR01FitQualityCurved1D, dr01_quality_curved_from_sample_kw


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


@dataclass(frozen=True)
class DR01FitCurved1D:
    """Curvature-aware 1D DR fit artifact.

    Parameters:
    - u is fixed in current evidence sources (k > 0 only), typically u=0.
    - c0 is the k->0 limit of omega/k (interpretable as a sound speed proxy).
    - beta controls the leading curvature in omega/k vs k^2.
    """

    u: float
    c0: float
    beta: float

    tag: str = "synthetic_curved"

    source_kind: Literal["csv", "manual", "synthetic", "unknown"] = "unknown"
    source_ref: str | None = None

    data_fingerprint: str | None = None
    sample_kw: tuple[tuple[float, float], ...] | None = None

    fit_method_tag: str = "unspecified"

    # Optional stamped quality metadata (computed from sample_kw).
    fit_quality: DR01FitQualityCurved1D | None = None
    fit_quality_fingerprint: str | None = None

    def __post_init__(self) -> None:
        if self.sample_kw is not None and self.data_fingerprint is None:
            object.__setattr__(
                self,
                "data_fingerprint",
                DR01Fit1D.data_fingerprint_from_sample(self.sample_kw),
            )

        if self.sample_kw is not None and self.fit_quality is None:
            q = dr01_quality_curved_from_sample_kw(self.sample_kw)
            object.__setattr__(self, "fit_quality", q)
            object.__setattr__(self, "fit_quality_fingerprint", q.fingerprint())

        if self.fit_quality is not None and self.fit_quality_fingerprint is None:
            object.__setattr__(self, "fit_quality_fingerprint", self.fit_quality.fingerprint())

    def omega_over_k(self, k: float) -> float:
        if k == 0.0:
            return float(self.c0)
        return float(self.u + self.c0 + self.beta * (k * k))

    def omega(self, k: float) -> float:
        # Keep the |k| structure for potential future negative-k usage.
        kk = float(k)
        return float(self.u * kk + self.c0 * abs(kk) + self.beta * (abs(kk) ** 3))

    def fingerprint(self) -> str:
        dfp = self.data_fingerprint if self.data_fingerprint is not None else "none"
        src = self.source_ref if self.source_ref is not None else "none"
        qfp = self.fit_quality_fingerprint if self.fit_quality_fingerprint is not None else "none"
        return (
            f"{self.tag}"
            f"|u={float(self.u):.16g}"
            f"|c0={float(self.c0):.16g}"
            f"|beta={float(self.beta):.16g}"
            f"|source_kind={self.source_kind}"
            f"|source_ref={src}"
            f"|fit_method={self.fit_method_tag}"
            f"|data_fingerprint={dfp}"
            f"|fit_quality_fingerprint={qfp}"
        )


def dr01_fit_curved_from_sample_kw(
    sample_kw: Iterable[tuple[float, float]],
    *,
    u_fixed: float = 0.0,
    tag: str = "computed_curved",
    source_kind: Literal["csv", "manual", "synthetic", "unknown"] = "unknown",
    source_ref: str | None = None,
    fit_method_tag: str = "low-k curved omega_over_k: omega/k = c0 + beta*k^2; u fixed",
) -> DR01FitCurved1D:
    """Deterministically fit the curvature-aware model to a frozen sample."""

    items = [(float(k), float(w)) for (k, w) in sample_kw]
    if len(items) < 3:
        raise ValueError("Need at least 3 points to fit (c0, beta) with stderr")

    ks = [k for (k, _) in items]
    ws = [w for (_, w) in items]

    ys = [w / k for (k, w) in zip(ks, ws)]
    xs = [k * k for k in ks]

    n = len(xs)
    xbar = sum(xs) / n
    ybar = sum(ys) / n

    sxx = sum((x - xbar) * (x - xbar) for x in xs)
    if sxx == 0.0:
        raise ValueError("Degenerate sample: var(k^2) == 0")

    sxy = sum((x - xbar) * (y - ybar) for (x, y) in zip(xs, ys))

    beta = sxy / sxx
    c0 = ybar - beta * xbar

    q = dr01_quality_curved_from_sample_kw(items)

    return DR01FitCurved1D(
        u=float(u_fixed),
        c0=float(c0),
        beta=float(beta),
        tag=str(tag),
        source_kind=source_kind,
        source_ref=source_ref,
        sample_kw=tuple(items),
        data_fingerprint=DR01Fit1D.data_fingerprint_from_sample(items),
        fit_method_tag=str(fit_method_tag),
        fit_quality=q,
        fit_quality_fingerprint=q.fingerprint(),
    )
