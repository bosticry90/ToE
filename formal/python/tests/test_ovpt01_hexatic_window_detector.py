from __future__ import annotations

import numpy as np

from formal.python.toe.observables.ovpt01_phase_transition_window_audit import ovpt01_detect_hexatic_window


def test_ovpt01_detects_hexatic_like_window_on_synthetic_data():
    T = np.linspace(0.0, 1.0, 21)

    # Translational order drops earlier.
    transl = np.where(T < 0.4, 0.9, 0.1)

    # Orientational order drops later.
    orient = np.where(T < 0.7, 0.9, 0.2)

    rep = ovpt01_detect_hexatic_window(
        T=T,
        transl_order=transl,
        orient_order=orient,
        transl_threshold=0.3,
        orient_threshold=0.6,
    )

    assert rep.has_hexatic_window
    assert rep.n_samples == len(T)
    assert rep.window_T_low is not None
    assert rep.window_T_high is not None
    assert rep.window_T_low >= 0.4
    assert rep.window_T_high <= 0.7


def test_ovpt01_no_window_when_orders_drop_together():
    T = np.linspace(0.0, 1.0, 21)
    transl = np.where(T < 0.5, 0.9, 0.1)
    orient = np.where(T < 0.5, 0.9, 0.2)

    rep = ovpt01_detect_hexatic_window(T=T, transl_order=transl, orient_order=orient)
    assert not rep.has_hexatic_window
    assert rep.n_samples == len(T)
