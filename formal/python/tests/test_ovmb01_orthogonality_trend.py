from __future__ import annotations

from formal.python.toe.observables.ovmb01_orthogonality_catastrophe_audit import ovmb01_orthogonality_trend_audit


def test_ovmb01_overlap_is_sensitive_to_impurity_strength():
    # Finite-size ring overlaps oscillate with L; this audit is a toy scaffold.
    # We assert only robust invariants:
    # - With V=0, the two Hamiltonians are identical, so overlap ≈ 1.
    # - Increasing V at fixed L decreases the overlap (stronger perturbation).

    L = 24
    filling = 0.25

    rep0 = ovmb01_orthogonality_trend_audit(L_values=(L,), filling=filling, t=1.0, V=0.0)
    rep1 = ovmb01_orthogonality_trend_audit(L_values=(L,), filling=filling, t=1.0, V=1.0)
    rep5 = ovmb01_orthogonality_trend_audit(L_values=(L,), filling=filling, t=1.0, V=5.0)

    assert abs(rep0.filling - filling) < 1e-12

    ov0 = rep0.points[0].overlap
    ov1 = rep1.points[0].overlap
    ov5 = rep5.points[0].overlap

    eps = 1e-9
    assert -eps <= ov0 <= 1.0 + eps
    assert -eps <= ov1 <= 1.0 + eps
    assert -eps <= ov5 <= 1.0 + eps

    assert abs(ov0 - 1.0) < 1e-10
    assert ov5 < ov1 < ov0
