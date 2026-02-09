import sympy as sp

from equations.ucff_core import (
    # coordinates, symbols
    x,
    t,
    k,
    omega,
    # fields and parameters
    phi,
    rho,
    rho0,
    g,
    lam,
    beta,
    lambda_coh,
    # core Lagrangian and dispersion
    ucff_lagrangian_first_order,
    ucff_dispersion_first_order,
    ucff_dispersion_second_order,
)


def _density(field: sp.Expr) -> sp.Expr:
    return sp.conjugate(field) * field


# ---------------------------------------------------------------------------
# Lagrangian-level coherence structure
# ---------------------------------------------------------------------------


def test_ucff_lagrangian_first_order_contains_coherence():
    """
    The first-order UCFF Lagrangian must:

      - contain lam,
      - contain the coherence density structure (rho_x)^2 / (4 rho).

    We test for the presence of lam, (∂_x rho)^2, and 1/rho.
    """
    L1 = ucff_lagrangian_first_order()

    rho_x = sp.diff(rho, x)

    # lam present
    assert L1.has(lam)

    # Coherence density structure is present:
    # (∂_x rho)^2 and 1/rho (up to overall factors).
    assert L1.has(rho_x**2)
    assert L1.has(1 / rho)


# ---------------------------------------------------------------------------
# Dispersion: structural checks in k
# ---------------------------------------------------------------------------


def test_ucff_dispersion_first_order_structure():
    """
    First-order UCFF dispersion must have the Bogoliubov form

        ω² = (k²/2)² + (g ρ0) k² + lam k⁴

    at the level of symbolic structure.

    To avoid false negatives due to factorization (e.g. k² * (g ρ0 + …)),
    we expand in k before checking for k⁴.
    """
    disp = ucff_dispersion_first_order()
    assert isinstance(disp, sp.Equality)

    rhs = sp.simplify(disp.rhs)
    rhs_expanded = sp.expand(rhs)

    # k-power structure
    assert rhs_expanded.has(k**2)
    assert rhs_expanded.has(k**4)

    # parameter structure
    assert rhs_expanded.has(g)
    assert rhs_expanded.has(rho0)
    assert rhs_expanded.has(lam)


def test_ucff_dispersion_second_order_structure():
    """
    Second-order UCFF dispersion must extend the first-order one with
    a beta k^6 term:

        ω² = (k²/2)² + (g ρ0) k² + lam k⁴ + beta k⁶.

    Again we expand in k to make the presence of k⁶ explicit at the
    expression-tree level.
    """
    disp = ucff_dispersion_second_order()
    assert isinstance(disp, sp.Equality)

    rhs = sp.simplify(disp.rhs)
    rhs_expanded = sp.expand(rhs)

    # k-power structure
    assert rhs_expanded.has(k**2)
    assert rhs_expanded.has(k**4)
    assert rhs_expanded.has(k**6)

    # parameter structure
    assert rhs_expanded.has(g)
    assert rhs_expanded.has(rho0)
    assert rhs_expanded.has(lam)
    assert rhs_expanded.has(beta)
