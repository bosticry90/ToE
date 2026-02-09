from __future__ import annotations

from formal.python.toe.observables.ovqc01_berry_curvature_audit import ovqc01_chern_number_qiwuzhang


def test_ovqc01_qiwuzhang_chern_matches_known_phase():
    # For -2 < m < 0, the QWZ model has Chern number +1.
    rep = ovqc01_chern_number_qiwuzhang(m=-1.0, grid_n=25)
    assert rep.model == "qiwuzhang"
    assert abs(rep.m - (-1.0)) < 1e-12
    # Sign depends on Hamiltonian/sign conventions; magnitude is the invariant.
    assert abs(rep.chern_number) == 1

    # For |m| > 2, trivial phase.
    rep2 = ovqc01_chern_number_qiwuzhang(m=3.0, grid_n=25)
    assert rep2.model == "qiwuzhang"
    assert rep2.chern_number == 0
