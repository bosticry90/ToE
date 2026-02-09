"""EMP-01 — Behavioral (Python) proxy falsifiability probe (simulation-only).

What this is
------------
- A synthetic, deterministic behavior check that depends only on the DR-01→BR-01
  artifact chain.
- A *proxy falsifier* for a narrowly scoped expectation about internal pipeline
  consistency.

What this is NOT
----------------
- Not empirical validation.
- Not confirmation of the ToE program.
- Not a governance hook: it must not be used by gates, pruning, or lock regen.
- Not a status-upgrading mechanism.

What it outputs
---------------
- A deterministic report dict, including a pass/fail boolean for exactly one
  falsifier condition.

What failure means
------------------
- Failure falsifies this proxy expectation only ("BR-01 metric prediction matches
  DR-01 omega(k) on a fixed k-grid under the current mapping").
- Failure does NOT retroactively refute upstream locks or formal structure.

Invariant / governance isolation
--------------------------------
EMP-01 must not be imported or referenced by:
- formal/python/tools/regen_canonical_locks.py
- any pruning table builders
- any admissibility gate checks
- any selection/audit records that affect candidate survival

This module intentionally contains no filesystem I/O.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
from typing import Iterable, Sequence

import numpy as np

from formal.python.toe.bridges.br01_dispersion_to_metric import (
    br01_metric_from_DR01_fit,
    br01_predict_omega_from_metric_1d,
)
from formal.python.toe.dr01_fit import DR01Fit1D


@dataclass(frozen=True)
class EMP01Report:
    """Deterministic EMP-01 report.

    Note: `passed` is *non-confirmatory*.
    """

    emp_id: str
    mode: str

    dr01_fingerprint: str
    data_fingerprint: str | None

    k_grid: tuple[float, ...]

    max_abs_omega_residual: float
    tol: float

    passed: bool

    banner: str
    interpretation_guardrail: str


def _canonical_k_grid(k_grid: Iterable[float]) -> tuple[float, ...]:
    ks = [float(k) for k in k_grid]
    if len(ks) == 0:
        raise ValueError("k_grid must be non-empty")
    # Deterministic ordering: preserve order as given, but validate.
    for k in ks:
        if not np.isfinite(k):
            raise ValueError("k_grid contains non-finite value")
    return tuple(ks)


def emp01_proxy_falsifiability_probe(
    dr01_fit: DR01Fit1D,
    *,
    k_grid: Sequence[float],
    tol: float,
) -> EMP01Report:
    """Run the EMP-01 proxy falsifiability probe.

    Proxy claim (single falsifier):
        max_k | omega_DR01(k) - omega_BR01(metric_from_DR01)(k) | <= tol

    This is intentionally non-confirmatory: passing means only "not falsified
    under this proxy".
    """

    if tol <= 0.0 or not np.isfinite(float(tol)):
        raise ValueError("tol must be finite and > 0")

    ks = _canonical_k_grid(k_grid)

    metric = br01_metric_from_DR01_fit(dr01_fit, n=1)

    residuals: list[float] = []
    for k in ks:
        w_fit = float(dr01_fit.omega(k))
        w_metric = float(br01_predict_omega_from_metric_1d(metric, float(k)))
        residuals.append(abs(w_fit - w_metric))

    max_abs = float(np.max(np.asarray(residuals, dtype=float)))
    passed = bool(max_abs <= float(tol))

    return EMP01Report(
        emp_id="EMP-01",
        mode="synthetic_simulation_only",
        dr01_fingerprint=dr01_fit.fingerprint(),
        data_fingerprint=dr01_fit.data_fingerprint,
        k_grid=ks,
        max_abs_omega_residual=max_abs,
        tol=float(tol),
        passed=passed,
        banner="SYNTHETIC ONLY — NON-EMPIRICAL — NON-CONFIRMATORY",
        interpretation_guardrail=(
            "A pass is not a confirmation; it only indicates the proxy falsifier did not trigger. "
            "A failure falsifies only this proxy expectation and does not refute upstream locks." 
        ),
    )


def emp01_proxy_falsifiability_report_dict(
    dr01_fit: DR01Fit1D,
    *,
    k_grid: Sequence[float],
    tol: float,
) -> dict:
    """Convenience wrapper returning a plain dict (stable for tests/logging)."""

    rep = emp01_proxy_falsifiability_probe(dr01_fit, k_grid=k_grid, tol=tol)
    return asdict(rep)
