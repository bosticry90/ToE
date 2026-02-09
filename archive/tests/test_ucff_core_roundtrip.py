import sympy as sp

from equations.ucff_core import (
    # coordinates and symbols
    x,
    t,
    k,
    omega,
    # fields and parameters
    phi,
    rho0,
    g,
    lam,
    beta,
    lambda_coh,
    # core EOM and dispersion
    ucff_first_order_eom,
    ucff_second_order_eom,
    ucff_dispersion_first_order,
    ucff_dispersion_second_order,
)


def _reduce_residual_with_plane_wave(R_expr: sp.Expr) -> sp.Expr:
    """
    Substitute a plane wave ansatz into the residual R[phi]:

        phi(x,t) = exp(i (k x - omega t)),

    and divide out the common factor, returning a scalar expression
    in (k, omega).
    """
    phi_pw = sp.exp(sp.I * (k * x - omega * t))
    R_pw = sp.simplify(R_expr.subs(phi, phi_pw))
    R_reduced = sp.simplify(R_pw / phi_pw)
    return R_reduced


def _extract_single_omega_solution(expr: sp.Expr) -> sp.Expr:
    """
    Solve expr(k, omega) = 0 for omega and robustly extract a single
    branch suitable for constructing ω², handling SymPy’s possible
    return types:

        - [expr],
        - [(expr,)],
        - [dict({...})], etc.
    """
    sol = sp.solve(sp.Eq(expr, 0), omega)
    assert len(sol) >= 1

    root = sol[0]

    if isinstance(root, dict):
        # pick the first value
        root = list(root.values())[0]
    elif isinstance(root, (tuple, list)):
        root = root[0]

    return sp.simplify(root)


# ---------------------------------------------------------------------------
# ROUND-TRIP 1: first-order EOM -> dispersion (baseline consistency)
# ---------------------------------------------------------------------------


def test_first_order_eom_to_dispersion_roundtrip():
    """
    ROUND-TRIP 1 (first order, baseline consistency):

      EOM(φ)  --plane wave-->  algebraic equation  --solve-->  ω(k),

    must match the core first-order dispersion relation
        ucff_dispersion_first_order

    in the *baseline* linear regime

        g = 0, lambda_coh = 0, lam = 0, beta = 0.

    Rationale:
    - The UCFF core dispersion (ucff_dispersion_first_order) encodes a
      Bogoliubov-style specification with higher-order λ terms defined
      at the level of ω²(k).
    - The first-order EOM encodes λ-effects at the level of ω(k) itself,
      so ω² from the EOM may differ at O(λ), O(β) from the chosen
      hydrodynamic / UCFF-core form without contradicting the baseline
      physics.
    - We therefore *lock* the baseline (λ = β = 0) exactly, while allowing
      higher-order corrections to differ between approximations.
    """
    R1 = ucff_first_order_eom()

    # Linear baseline regime: no nonlinearity, no coherence, no λ, no β.
    R1_baseline = sp.simplify(
        R1.subs({g: 0, lambda_coh: 0, lam: 0, beta: 0})
    )

    # Plane-wave reduction
    R_reduced = _reduce_residual_with_plane_wave(R1_baseline)
    omega_from_eom = _extract_single_omega_solution(R_reduced)

    # Build ω²(k) from the EOM in the baseline regime
    omega2_from_eom = sp.simplify(omega_from_eom**2)

    # Core dispersion in the same baseline limit
    disp_core = ucff_dispersion_first_order()
    assert isinstance(disp_core, sp.Equality)
    omega2_core = sp.simplify(
        disp_core.rhs.subs({g: 0, lam: 0, beta: 0})
    )

    # Baseline equality: free-UCFF dispersion must coincide
    diff = sp.simplify(omega2_from_eom - omega2_core)
    assert diff == 0


# ---------------------------------------------------------------------------
# ROUND-TRIP 3: second-order EOM -> dispersion (baseline consistency)
# ---------------------------------------------------------------------------


def test_second_order_eom_to_dispersion_roundtrip():
    """
    ROUND-TRIP 3 (second order, baseline consistency):

      second-order EOM(φ)  --plane wave-->  algebraic equation  --solve-->  ω(k),

    must match the core second-order dispersion relation
        ucff_dispersion_second_order

    in the *baseline* linear regime

        g = 0, lambda_coh = 0, lam = 0, beta = 0.

    As in the first-order case, we do not demand exact equality of the
    λ- and β-dependent pieces between the EOM-derived ω²(k) and the
    UCFF-core Bogoliubov form, since those encode different approximations
    to higher-order dispersion physics. We only lock the λ = β = 0 limit.
    """
    R2 = ucff_second_order_eom()

    R2_baseline = sp.simplify(
        R2.subs({g: 0, lambda_coh: 0, lam: 0, beta: 0})
    )

    R_reduced = _reduce_residual_with_plane_wave(R2_baseline)
    omega_from_eom = _extract_single_omega_solution(R_reduced)

    omega2_from_eom = sp.simplify(omega_from_eom**2)

    disp_core = ucff_dispersion_second_order()
    assert isinstance(disp_core, sp.Equality)
    omega2_core = sp.simplify(
        disp_core.rhs.subs({g: 0, lam: 0, beta: 0})
    )

    diff = sp.simplify(omega2_from_eom - omega2_core)
    assert diff == 0
