"""
crft/diagnostics/acoustic_metric.py

Acoustic-metric-style diagnostics for CRFT hydrodynamic fields.

This module defines purely diagnostic, non-dynamical quantities derived
from CRFT hydrodynamic variables (rho, u). It follows the Extended CRFT
C7 specification:

    c_s^2 = g_eff * rho

    g_tt = -(c_s^2 - |u|^2)
    g_tx = -u_x
    g_ty = -u_y
    g_xx = g_yy = 1

Here u_x, u_y are the components of the velocity vector (not derivatives),
and |u|^2 = u_x^2 + u_y^2 in 2D.

The functions below implement 1D and 2D versions of these diagnostics and
expose helpers to compute the determinant of the metric in each case.
All operations are per-grid-point and vectorized over NumPy arrays.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict

import numpy as np


@dataclass
class AcousticMetric1D:
    """
    Container for the 1+1D acoustic metric components.

    Fields:

        g_tt : ndarray
            Time-time component, shape (N,).
        g_tx : ndarray
            Mixed time-space component, shape (N,).
        g_xx : ndarray
            Spatial component, typically ones, shape (N,).
        c_s2 : ndarray
            Effective sound speed squared, c_s^2 = g_eff * rho.
    """

    g_tt: np.ndarray
    g_tx: np.ndarray
    g_xx: np.ndarray
    c_s2: np.ndarray


@dataclass
class AcousticMetric2D:
    """
    Container for the 1+2D acoustic metric components.

    Fields:

        g_tt : ndarray
            Time-time component, shape (Ny, Nx) or (N, M).
        g_tx : ndarray
            Mixed t-x component, shape (Ny, Nx).
        g_ty : ndarray
            Mixed t-y component, shape (Ny, Nx).
        g_xx : ndarray
            Spatial x-x component, typically ones, shape (Ny, Nx).
        g_yy : ndarray
            Spatial y-y component, typically ones, shape (Ny, Nx).
        c_s2 : ndarray
            Effective sound speed squared, c_s^2 = g_eff * rho.
    """

    g_tt: np.ndarray
    g_tx: np.ndarray
    g_ty: np.ndarray
    g_xx: np.ndarray
    g_yy: np.ndarray
    c_s2: np.ndarray


def compute_acoustic_metric_1d(
    rho: np.ndarray,
    u: np.ndarray,
    g_eff: float,
) -> AcousticMetric1D:
    """
    Compute the 1+1D acoustic metric components for a 1D CRFT hydrodynamic
    configuration.

    Parameters
    ----------
    rho : ndarray, shape (N,)
        Density field.
    u : ndarray, shape (N,)
        Velocity field (x-component).
    g_eff : float
        Effective coupling, c_s^2 = g_eff * rho.

    Returns
    -------
    AcousticMetric1D
        Container with g_tt, g_tx, g_xx, and c_s2.
    """
    rho = np.asarray(rho)
    u = np.asarray(u)

    # Effective sound speed squared
    c_s2 = g_eff * rho

    # |u|^2 in 1D is simply u^2
    u_sq = u ** 2

    # Metric components from the C7 specification
    g_tt = -(c_s2 - u_sq)
    g_tx = -u
    g_xx = np.ones_like(rho)

    return AcousticMetric1D(g_tt=g_tt, g_tx=g_tx, g_xx=g_xx, c_s2=c_s2)


def metric_determinant_1d(metric: AcousticMetric1D) -> np.ndarray:
    """
    Compute the determinant of the 1+1D metric at each grid point.

    For the 2x2 matrix:

        g = [[g_tt, g_tx],
             [g_tx, g_xx]]

    the determinant is:

        det(g) = g_tt * g_xx - g_tx^2

    Returns
    -------
    det_g : ndarray, shape (N,)
        Determinant of the metric at each grid point.
    """
    g_tt = metric.g_tt
    g_tx = metric.g_tx
    g_xx = metric.g_xx
    det_g = g_tt * g_xx - g_tx ** 2
    return det_g


def compute_acoustic_metric_2d(
    rho: np.ndarray,
    u_x: np.ndarray,
    u_y: np.ndarray,
    g_eff: float,
) -> AcousticMetric2D:
    """
    Compute the 1+2D acoustic metric components for a 2D CRFT hydrodynamic
    configuration.

    Parameters
    ----------
    rho : ndarray, shape (Ny, Nx)
        Density field.
    u_x : ndarray, shape (Ny, Nx)
        x-component of velocity.
    u_y : ndarray, shape (Ny, Nx)
        y-component of velocity.
    g_eff : float
        Effective coupling, c_s^2 = g_eff * rho.

    Returns
    -------
    AcousticMetric2D
        Container with g_tt, g_tx, g_ty, g_xx, g_yy, and c_s2.
    """
    rho = np.asarray(rho)
    u_x = np.asarray(u_x)
    u_y = np.asarray(u_y)

    c_s2 = g_eff * rho
    u_sq = u_x ** 2 + u_y ** 2

    g_tt = -(c_s2 - u_sq)
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
    """
    Compute the determinant of the 1+2D metric at each grid point.

    For the 3x3 matrix (with vanishing off-diagonal spatial terms):

        g = [[g_tt, g_tx, g_ty],
             [g_tx, g_xx,    0],
             [g_ty,    0, g_yy]]

    the determinant simplifies to:

        det(g) = g_tt * g_xx * g_yy - g_tx^2 * g_yy - g_ty^2 * g_xx

    For the common case g_xx = g_yy = 1, this reduces to:

        det(g) = g_tt - (g_tx^2 + g_ty^2)

    Returns
    -------
    det_g : ndarray, shape (Ny, Nx)
        Determinant of the metric at each grid point.
    """
    g_tt = metric.g_tt
    g_tx = metric.g_tx
    g_ty = metric.g_ty
    g_xx = metric.g_xx
    g_yy = metric.g_yy

    det_g = g_tt * g_xx * g_yy - (g_tx ** 2) * g_yy - (g_ty ** 2) * g_xx
    return det_g
