from __future__ import annotations

from formal.python.tools.bridge_toyh_c6_phase_anchor import _phase_residual_stable


def test_bridge_toyh_phase_stabilization_residual_is_stable_near_zero() -> None:
    r12 = _phase_residual_stable(1e-12, 2e-12)
    r21 = _phase_residual_stable(2e-12, 1e-12)
    r00 = _phase_residual_stable(0.0, 0.0)
    r_large = _phase_residual_stable(0.0, 1e-6)

    assert r00 == 0.0
    assert r12 > 0.0
    assert r12 < 1e-9
    assert abs(r12 - r21) <= 1e-18
    assert r_large > r12
