"""BR-01 internal candidates (DO NOT import directly).

This module holds concrete mapping implementations for BR-01. Downstream code must
import the BR-01 front door in:
  formal.python.toe.bridges.br01_dispersion_to_metric

Enforcement lives in:
  formal/python/tests/test_br01_front_door_enforced.py
"""

from __future__ import annotations

import numpy as np

from formal.python.crft import acoustic_metric as mt01
from formal.python.toe.dr01_fit import DR01Fit1D


def BR01_metric_from_DR01_fit_unit_density(dr01_fit: DR01Fit1D, *, n: int = 1) -> mt01.AcousticMetric1D:
    """Candidate mapping: choose rho ≡ 1 and g_eff = c_s^2.

    Then c_s^2 = g_eff * rho holds definitionally and the acoustic metric encodes
    the (u, c_s) pair.
    """

    if n <= 0:
        raise ValueError("n must be positive")

    rho = np.ones((n,), dtype=float)
    u = np.full((n,), float(dr01_fit.u), dtype=float)
    g_eff = float(dr01_fit.c_s) ** 2
    return mt01.compute_acoustic_metric_1d(rho=rho, u=u, g_eff=g_eff)


def BR01_metric_from_DR01_fit_unit_density_structural_fail(
    dr01_fit: DR01Fit1D, *, n: int = 1
) -> mt01.AcousticMetric1D:
    """Candidate mapping: identical to unit-density baseline.

    This exists to support a discriminative structural pruning demonstration (one pass, one fail)
    without introducing any new numeric constraints.
    """

    return BR01_metric_from_DR01_fit_unit_density(dr01_fit, n=n)


def BR01_metric_from_DR01_fit_constant_density(
  dr01_fit: DR01Fit1D, *, n: int = 1, rho0: float = 2.0
) -> mt01.AcousticMetric1D:
  """Candidate mapping: choose rho ≡ rho0 and g_eff = c_s^2 / rho0.

  This encodes the same (u, c_s) pair but fixes a non-unit density scale.
  """

  if n <= 0:
    raise ValueError("n must be positive")
  if float(rho0) <= 0.0:
    raise ValueError("rho0 must be positive")

  rho = np.full((n,), float(rho0), dtype=float)
  u = np.full((n,), float(dr01_fit.u), dtype=float)
  g_eff = (float(dr01_fit.c_s) ** 2) / float(rho0)
  return mt01.compute_acoustic_metric_1d(rho=rho, u=u, g_eff=g_eff)


def BR01_metric_from_DR01_fit_rest_frame_u0(dr01_fit: DR01Fit1D, *, n: int = 1) -> mt01.AcousticMetric1D:
  """Candidate mapping: choose a rest-frame gauge u ≡ 0 with rho ≡ 1.

  This is a structurally plausible alternative mapping choice for BR-01.
  It is intentionally left without a formal BR-05 prediction declaration by
  default (status remains "unknown" in structural pruning).
  """

  if n <= 0:
    raise ValueError("n must be positive")

  rho = np.ones((n,), dtype=float)
  u = np.zeros((n,), dtype=float)
  g_eff = float(dr01_fit.c_s) ** 2
  return mt01.compute_acoustic_metric_1d(rho=rho, u=u, g_eff=g_eff)
