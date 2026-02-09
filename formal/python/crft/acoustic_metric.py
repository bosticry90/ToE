"""CRFT acoustic metric (MT-01).

This module is the canonical *Python-side* lock implementation for the
acoustic-metric formulas mirrored in Lean at:
  formal/toe_formal/ToeFormal/CRFT/Geom/AcousticMetric.lean

Scope: pointwise diagnostic construction only (no dynamics).
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np


@dataclass(frozen=True)
class AcousticMetric1D:
    g_tt: np.ndarray
    g_tx: np.ndarray
    g_xx: np.ndarray
    c_s2: np.ndarray


@dataclass(frozen=True)
class AcousticMetric2D:
    g_tt: np.ndarray
    g_tx: np.ndarray
    g_ty: np.ndarray
    g_xx: np.ndarray
    g_yy: np.ndarray
    c_s2: np.ndarray


def compute_acoustic_metric_1d(rho: np.ndarray, u: np.ndarray, g_eff: float) -> AcousticMetric1D:
    rho = np.asarray(rho)
    u = np.asarray(u)

    c_s2 = g_eff * rho
    g_tt = -(c_s2 - u**2)
    g_tx = -u
    g_xx = np.ones_like(rho)

    return AcousticMetric1D(g_tt=g_tt, g_tx=g_tx, g_xx=g_xx, c_s2=c_s2)


def metric_determinant_1d(metric: AcousticMetric1D) -> np.ndarray:
    return metric.g_tt * metric.g_xx - metric.g_tx**2


def compute_acoustic_metric_2d(
    rho: np.ndarray,
    u_x: np.ndarray,
    u_y: np.ndarray,
    g_eff: float,
) -> AcousticMetric2D:
    rho = np.asarray(rho)
    u_x = np.asarray(u_x)
    u_y = np.asarray(u_y)

    c_s2 = g_eff * rho
    g_tt = -(c_s2 - u_x**2 - u_y**2)
    g_tx = -u_x
    g_ty = -u_y
    g_xx = np.ones_like(rho)
    g_yy = np.ones_like(rho)

    return AcousticMetric2D(
        g_tt=g_tt,
        g_tx=g_tx,
        g_ty=g_ty,
        g_xx=g_xx,
        g_yy=g_yy,
        c_s2=c_s2,
    )


def metric_determinant_2d(metric: AcousticMetric2D) -> np.ndarray:
    return metric.g_tt * metric.g_xx * metric.g_yy - (metric.g_tx**2) * metric.g_yy - (metric.g_ty**2) * metric.g_xx
