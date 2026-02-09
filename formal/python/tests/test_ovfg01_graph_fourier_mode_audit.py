from __future__ import annotations

import numpy as np

from formal.python.toe.observables.ovfg01_graph_fourier_mode_audit import ovfg01_graph_fourier_mode_audit


def test_ovfg01_ring_laplacian_fourier_modes_are_eigenmodes():
    n = 32
    dx = 0.5

    # Test a few nontrivial modes.
    for m in (1, 2, 3, 5, 7):
        rep = ovfg01_graph_fourier_mode_audit(n=n, dx=dx, mode_m=m)

        # Eigenvalue should match to tight tolerance (analytic formula).
        assert abs(rep.eigenvalue_observed - rep.eigenvalue_expected) < 1e-10

        # Mode purity: numerical error should be tiny.
        assert rep.mode_purity_l2_error < 1e-10


def test_ovfg01_zero_mode_has_zero_eigenvalue():
    rep = ovfg01_graph_fourier_mode_audit(n=16, dx=1.0, mode_m=0)
    assert abs(rep.eigenvalue_expected) < 1e-12
    assert abs(rep.eigenvalue_observed) < 1e-12
