"""Bridge attempt: C6 CP–NLSE linear dispersion ↔ UCFF core omega^2.

This is a bounded, deterministic, structural mapping only.
It does not claim empirical equivalence.
"""

from __future__ import annotations

import numpy as np

from formal.python.toe.ucff.core_front_door import UcffCoreParams, ucff_dispersion_omega2_numeric


def test_bridge_c6_ucff_omega2_equals_square_of_linear_c6_omega() -> None:
    # Deterministic k grid (non-negative magnitudes).
    k = np.asarray([0.0, 0.05, 0.1, 0.25, 0.5, 1.0, 2.0], dtype=float)

    # C6 linear Schrödinger limit (g_eff=0): omega(k) = 0.5 * k^2.
    omega_c6 = 0.5 * (k**2)
    omega2_c6 = omega_c6**2

    # UCFF core with g=lam=beta=0: omega^2(k) = (k^2/2)^2.
    params = UcffCoreParams(rho0=1.0, g=0.0, lam=0.0, beta=0.0)
    omega2_ucff = ucff_dispersion_omega2_numeric(k=k, params=params)

    assert np.allclose(omega2_ucff, omega2_c6, rtol=0.0, atol=0.0)
