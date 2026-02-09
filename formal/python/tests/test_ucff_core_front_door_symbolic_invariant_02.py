from __future__ import annotations

import sympy as sp

from formal.python.toe.ucff.core_front_door import UcffCoreInput, UcffCoreParams, ucff_core_report


def _R(x: float) -> sp.Rational:
    # Deterministic float->rational conversion for simple exact floats.
    return sp.Rational(str(float(x)))


def _recover_even_poly_coeffs_from_report(*, k: list[float], omega2: list[float]) -> dict[sp.Symbol, sp.Expr]:
    k_vals = [_R(x) for x in k]
    y_vals = [_R(y) for y in omega2]

    a0, a2, a4, a6 = sp.symbols("a0 a2 a4 a6")
    eqs = [sp.Eq(y, a0 + a2 * (kk**2) + a4 * (kk**4) + a6 * (kk**6)) for kk, y in zip(k_vals, y_vals)]
    sol = sp.solve(eqs, (a0, a2, a4, a6), dict=True)
    assert sol, "Expected SymPy to solve for even-polynomial coefficients"
    return sol[0]


def test_ucff_core_front_door_monotone_non_decreasing_on_bounded_interval_when_coeffs_nonnegative() -> None:
    """Second independent bounded invariant (symbolic-family): monotonicity.

    For an even polynomial in k of the form:

      p(k) = a0 + a2 k^2 + a4 k^4 + a6 k^6,

    if a2,a4,a6 >= 0 then p'(k) >= 0 for k >= 0.

    This is checked on a small deterministic grid on [0, k_max] using recovered
    coefficients from the UCFF front-door report.
    """

    params = UcffCoreParams(rho0=1.0, g=2.0, lam=0.25, beta=0.125)
    inp = UcffCoreInput(
        k=[0.0, 1.0, 2.0, 3.0],
        params=params,
        config_tag="pytest_ucff_core_symbolic_invariant_02",
    )

    rep = ucff_core_report(inp)
    coeffs = _recover_even_poly_coeffs_from_report(k=rep.k, omega2=rep.omega2)

    a0, a2, a4, a6 = sp.symbols("a0 a2 a4 a6")

    # Independent check axis: monotonicity on k>=0, derived from sign of derivative.
    # We do NOT re-assert the coefficient identities from invariant_01.
    p = coeffs[a0] + coeffs[a2] * (sp.Symbol("k") ** 2) + coeffs[a4] * (sp.Symbol("k") ** 4) + coeffs[a6] * (
        sp.Symbol("k") ** 6
    )

    k = sp.Symbol("k", real=True)
    p = coeffs[a0] + coeffs[a2] * (k**2) + coeffs[a4] * (k**4) + coeffs[a6] * (k**6)
    dp = sp.diff(p, k)

    # Bounded deterministic grid on [0, 3].
    grid = [sp.Rational(0, 1), sp.Rational(1, 4), sp.Rational(1, 2), sp.Rational(1, 1), sp.Rational(3, 2), sp.Rational(2, 1), sp.Rational(3, 1)]

    for kk in grid:
        v = sp.simplify(dp.subs(k, kk))
        assert v >= 0, f"Expected dp/dk >= 0 for k={kk}, got {v}"
