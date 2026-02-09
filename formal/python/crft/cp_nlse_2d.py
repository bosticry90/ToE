"""
crft/cp_nlse_2d.py

Extended CRFT 2D CP–NLSE (authoritative implementation).

Governing PDE (Equation Inventory v8, 2D extension):

    i φ_t = −(1/2) Δ φ + g_eff (|φ|^2 − rho0) φ

where:
    φ(x, y, t) complex-valued
    Δ = ∂xx + ∂yy (2D Laplacian)
    g_eff = 9.8696 (from LSDA → CRFT calibration)
    rho0  = 1.0 (background density)

Diagnostics (for reference):
    - 2D norm:
        N_2D = ∫∫ |φ|^2 dx dy
    - 2D energy (for lam = beta = 0):
        e_2D = 1/2 |∇φ|^2 + (g_eff/2) (|φ|^2 − rho0)^2
        E_2D = ∫∫ e_2D dx dy

Spatial derivatives are computed spectrally on a 2D periodic domain.

This module also provides a small, stable API used by regression tests:
    - Grid2D
    - CPParams2D  (backwards compatible: accepts g as alias for g_eff)
    - rhs_cp_nlse_2d
    - simulate_cp_nlse_2d
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Optional, Tuple

import numpy as np


@dataclass
class Grid2D:
    """
    2D periodic grid for spectral CP–NLSE.

    Attributes
    ----------
    Nx, Ny : int
        Number of grid points in x and y.
    Lx, Ly : float
        Physical domain lengths in x and y.
    x, y : np.ndarray
        Real-space grid points, shapes (Nx,) and (Ny,).
    kx, ky : np.ndarray
        Spectral wavenumbers, shapes (Nx, Ny) and (Nx, Ny).
    dx, dy : float
        Grid spacings in x and y.
    """

    Nx: int
    Ny: int
    Lx: float
    Ly: float

    def __post_init__(self) -> None:
        self.dx = self.Lx / self.Nx
        self.dy = self.Ly / self.Ny

        x1d = np.linspace(0.0, self.Lx, self.Nx, endpoint=False)
        y1d = np.linspace(0.0, self.Ly, self.Ny, endpoint=False)
        self.x, self.y = np.meshgrid(x1d, y1d, indexing="ij")

        kx_1d = 2.0 * np.pi * np.fft.fftfreq(self.Nx, d=self.dx)
        ky_1d = 2.0 * np.pi * np.fft.fftfreq(self.Ny, d=self.dy)
        self.kx, self.ky = np.meshgrid(kx_1d, ky_1d, indexing="ij")

    @classmethod
    def from_box(cls, Nx: int, Ny: int, Lx: float, Ly: float) -> "Grid2D":
        """Convenience constructor used by tests."""
        return cls(Nx=Nx, Ny=Ny, Lx=Lx, Ly=Ly)


@dataclass
class CPParams2D:
    """
    Parameter container for the 2D CP–NLSE.

    Backwards-compatibility note:
      Some tests historically used CPParams2D(g=..., rho0=...).
      Here, g is treated as an alias for g_eff.
    """

    g_eff: float = 9.8696
    rho0: float = 1.0

    def __init__(self, g_eff: float = 9.8696, rho0: float = 1.0, g: Optional[float] = None):
        if g is not None:
            g_eff = float(g)
        self.g_eff = float(g_eff)
        self.rho0 = float(rho0)


# Compatibility alias (older code may refer to this name)
CP_NLSE_2D_Params = CPParams2D


def laplacian_2d(field: np.ndarray, grid: Grid2D) -> np.ndarray:
    """
    Compute the 2D Laplacian using FFTs with periodic BCs.
    """
    F = np.fft.fft2(field)
    k2 = grid.kx ** 2 + grid.ky ** 2
    lapF = -(k2) * F
    return np.fft.ifft2(lapF)


def grad2_2d(field: np.ndarray, grid: Grid2D) -> Tuple[np.ndarray, np.ndarray]:
    """
    Compute (∂x field, ∂y field) using FFTs.
    """
    F = np.fft.fft2(field)
    fx = np.fft.ifft2(1j * grid.kx * F)
    fy = np.fft.ifft2(1j * grid.ky * F)
    return fx, fy


def rhs_cp_nlse_2d(phi: np.ndarray, grid: Grid2D, params: CPParams2D) -> np.ndarray:
    """
    Compute φ_t from:

        i φ_t = −1/2 Δ φ + g_eff (|φ|^2 − rho0) φ

    =>  φ_t = i [ 0.5 Δ φ − g_eff (|φ|^2 − rho0) φ ]

    For the linear Schrödinger limit used in dispersion tests:
        set params.g_eff = 0  (or CPParams2D(g=0.0)).
    """
    phi = np.asarray(phi, dtype=np.complex128)

    lap_phi = laplacian_2d(phi, grid)
    abs_sq = np.abs(phi) ** 2
    rho_diff = abs_sq - params.rho0

    return 1j * (0.5 * lap_phi - params.g_eff * rho_diff * phi)


def rk4_step_cp_nlse_2d(phi: np.ndarray, grid: Grid2D, params: CPParams2D, dt: float) -> np.ndarray:
    """
    Single explicit RK4 step.
    """
    k1 = rhs_cp_nlse_2d(phi, grid, params)
    k2 = rhs_cp_nlse_2d(phi + 0.5 * dt * k1, grid, params)
    k3 = rhs_cp_nlse_2d(phi + 0.5 * dt * k2, grid, params)
    k4 = rhs_cp_nlse_2d(phi + dt * k3, grid, params)
    return phi + (dt / 6.0) * (k1 + 2.0 * k2 + 2.0 * k3 + k4)


def simulate_cp_nlse_2d(
    t0: float,
    psi0: np.ndarray,
    dt: float,
    n_steps: int,
    rhs: Callable[[np.ndarray, Grid2D, CPParams2D], np.ndarray],
    grid: Grid2D,
    params: CPParams2D,
    sample_callback: Optional[Callable[[float, np.ndarray], None]] = None,
) -> np.ndarray:
    """
    Minimal simulation loop used by tests.

    Parameters
    ----------
    t0 : float
        Start time.
    psi0 : np.ndarray
        Initial complex field, shape (Nx, Ny).
    dt : float
        Time step.
    n_steps : int
        Number of steps.
    rhs : callable
        RHS function (typically rhs_cp_nlse_2d).
    grid : Grid2D
        Grid instance.
    params : CPParams2D
        Parameter container.
    sample_callback : callable or None
        If provided, called as sample_callback(t, psi) each step (including t0).

    Returns
    -------
    np.ndarray
        Final field.
    """
    psi = np.asarray(psi0, dtype=np.complex128).copy()
    t = float(t0)

    if sample_callback is not None:
        sample_callback(t, psi)

    # Use rk4_step_cp_nlse_2d to ensure consistent integration behavior
    for _ in range(int(n_steps)):
        psi = rk4_step_cp_nlse_2d(psi, grid, params, dt)
        t += dt
        if sample_callback is not None:
            sample_callback(t, psi)

    return psi


def compute_norm_2d(phi: np.ndarray, grid: Grid2D) -> float:
    phi = np.asarray(phi, dtype=np.complex128)
    density = np.abs(phi) ** 2
    return float(np.sum(density) * grid.dx * grid.dy)


def compute_energy_2d(phi: np.ndarray, grid: Grid2D, params: CPParams2D) -> float:
    phi = np.asarray(phi, dtype=np.complex128)
    phi_x, phi_y = grad2_2d(phi, grid)
    grad_sq = np.abs(phi_x) ** 2 + np.abs(phi_y) ** 2

    abs_sq = np.abs(phi) ** 2
    rho_diff = abs_sq - params.rho0
    e = 0.5 * grad_sq + 0.5 * params.g_eff * rho_diff ** 2
    return float(np.sum(e) * grid.dx * grid.dy)


__all__ = [
    "Grid2D",
    "CPParams2D",
    "CP_NLSE_2D_Params",
    "laplacian_2d",
    "grad2_2d",
    "rhs_cp_nlse_2d",
    "rk4_step_cp_nlse_2d",
    "simulate_cp_nlse_2d",
    "compute_norm_2d",
    "compute_energy_2d",
]
