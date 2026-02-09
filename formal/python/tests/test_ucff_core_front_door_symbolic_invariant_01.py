from __future__ import annotations

import sympy as sp

from formal.python.toe.ucff.core_front_door import UcffCoreInput, UcffCoreParams, ucff_core_report


def _R(x: float) -> sp.Rational:
    # Deterministic float->rational conversion for simple exact floats
    # used in this test (powers of two and small halves/quarters).
    return sp.Rational(str(float(x)))


def test_ucff_core_front_door_recovers_even_polynomial_coefficients_via_sympy() -> None:
    """Ported bounded invariant (symbolic-family): dispersion coefficient structure.

    Clean-room restatement of the legacy symbolic dispersion-structure tests:
    treat the UCFF core front door as authoritative, then use SymPy to recover
    the even-polynomial coefficients from the numeric report and compare them
    to the expected UCFF-like form.

    This avoids introducing a separate symbolic public surface.
    """

    # Choose parameters and k-grid values that keep all intermediate values exactly
    # representable (powers of two and halves/quarters) so the report is fully
    # deterministic and exact under rational reconstruction.
    params = UcffCoreParams(rho0=1.0, g=2.0, lam=0.25, beta=0.125)
    inp = UcffCoreInput(
        k=[0.0, 1.0, 2.0, 3.0],
        params=params,
        config_tag="pytest_ucff_core_symbolic_invariant_01",
    )

    rep = ucff_core_report(inp)

    k_vals = [_R(x) for x in rep.k]
    y_vals = [_R(y) for y in rep.omega2]

    a0, a2, a4, a6 = sp.symbols("a0 a2 a4 a6")
    eqs = [sp.Eq(y, a0 + a2 * (k**2) + a4 * (k**4) + a6 * (k**6)) for k, y in zip(k_vals, y_vals)]

    sol = sp.solve(eqs, (a0, a2, a4, a6), dict=True)
    assert sol, "Expected SymPy to solve for even-polynomial coefficients"
    coeffs = sol[0]

    expected_a0 = sp.Rational(0, 1)
    expected_a2 = _R(params.g) * _R(params.rho0)
    expected_a4 = sp.Rational(1, 4) + _R(params.lam)  # (k^2/2)^2 contributes k^4/4
    expected_a6 = _R(params.beta)

    assert sp.simplify(coeffs[a0] - expected_a0) == 0
    assert sp.simplify(coeffs[a2] - expected_a2) == 0
    assert sp.simplify(coeffs[a4] - expected_a4) == 0
    assert sp.simplify(coeffs[a6] - expected_a6) == 0
