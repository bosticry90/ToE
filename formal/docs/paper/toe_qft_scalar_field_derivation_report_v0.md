# ToE QFT Scalar Field Derivation Report v0

Report ID:
- `toe_qft_scalar_field_derivation_report_v0`

Scope:
- Phase 1 kickoff derivation from the master action to scalar Euler-Lagrange equations.
- Target mapping to Klein-Gordon-class structure under declared assumptions.

Master action slice (scalar sector declaration):
- Start from master action density and isolate a scalar lane with effective Lagrangian density
  `L_scalar = 1/2 d_mu phi d^mu phi - 1/2 m_eff^2 phi^2 - V_int(phi)`
  where `V_int(phi)` may be zero for free-field limit.

Declared assumptions:
1. `phi` is a smooth real scalar field on a Lorentzian background with metric signature `(+,-,-,-)`.
2. Boundary terms vanish under variation (compact support or asymptotic decay).
3. Coefficients in the scalar slice are treated as fixed during local variation.
4. For Klein-Gordon matching, use free-field regime `V_int(phi) = 0`.

Euler-Lagrange route:
- Use
  `d_mu (dL_scalar / d(d_mu phi)) - dL_scalar / dphi = 0`.
- Compute
  `dL_scalar / d(d_mu phi) = d^mu phi`.
- Compute
  `dL_scalar / dphi = -m_eff^2 phi - dV_int/dphi`.
- Therefore
  `box phi + m_eff^2 phi + dV_int/dphi = 0`.

Klein-Gordon-class map:
- Free-field limit (`dV_int/dphi = 0`) gives
  `(box + m_eff^2) phi = 0`,
  the Klein-Gordon-class equation.

Interpretation:
- The master-action scalar slice is compatible with relativistic scalar-field dynamics.
- Quantization route is deferred to Phase 3 while preserving this equation as the classical anchor.

Reproducibility pointers:
- `formal/output/toe_qft_scalar_field_equations_v0.json`
- `formal/python/tests/test_toe_qft_scalar_field_equation_gate.py`

Non-claim boundary:
- This report does not claim interacting renormalization completeness.
- This report does not claim full multi-field unification.
