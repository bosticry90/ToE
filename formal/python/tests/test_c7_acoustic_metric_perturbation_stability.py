from __future__ import annotations

import numpy as np

from formal.python.crft import acoustic_metric as mt01


def test_c7_acoustic_metric_sign_invariants_stable_under_small_perturbations_2d() -> None:
    # Independent bounded invariant (complements pointwise inequalities):
    # Under small deterministic perturbations of a subsonic admissible input family,
    # the sign invariants (g_tt < 0, det < 0) should remain unchanged.

    Nx, Ny = 10, 12
    rho0 = 1.7
    u0x = 0.05
    u0y = 0.03
    g_eff = 0.9

    rho = np.full((Nx, Ny), rho0)
    u_x = np.full((Nx, Ny), u0x)
    u_y = np.full((Nx, Ny), u0y)

    base = mt01.compute_acoustic_metric_2d(rho=rho, u_x=u_x, u_y=u_y, g_eff=g_eff)
    det_base = mt01.metric_determinant_2d(base)

    assert np.all(base.g_tt < 0.0)
    assert np.all(det_base < 0.0)

    # Deterministic perturbations: preserve positivity of rho and remain subsonic.
    eps = 1e-6
    rho_p = rho * (1.0 + eps)
    u_x_p = u_x + eps
    u_y_p = u_y - eps

    pert = mt01.compute_acoustic_metric_2d(rho=rho_p, u_x=u_x_p, u_y=u_y_p, g_eff=g_eff)
    det_pert = mt01.metric_determinant_2d(pert)

    assert np.all(pert.g_tt < 0.0)
    assert np.all(det_pert < 0.0)
