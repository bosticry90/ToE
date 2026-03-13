# ToE QFT Scalar Covariance Report v0

Report ID:
- `toe_qft_scalar_covariance_report_v0`

Scope:
- Phase 2 bounded verification for the scalar sector derived from the master action.
- Confirm relativistic scalar-field interpretation consistency with Klein-Gordon-class structure.

Input anchor:
- `formal/docs/paper/toe_qft_scalar_field_derivation_report_v0.md`
- `formal/output/toe_qft_scalar_field_equations_v0.json`

Covariance statement:
- Treat `phi(x)` as a Lorentz scalar field.
- Use scalar action density in flat background:
  `L_scalar = 1/2 d_mu phi d^mu phi - 1/2 m_eff^2 phi^2 - V_int(phi)`.
- Since `phi` is scalar and contraction uses `eta^{mu nu}`, the action is Lorentz invariant under declared assumptions.

Equation interpretation:
- Euler-Lagrange equation
  `box phi + m_eff^2 phi + dV_int/dphi = 0`
  transforms covariantly as a scalar equation.
- Free-field regime (`dV_int/dphi = 0`) gives Klein-Gordon class:
  `(box + m_eff^2) phi = 0`.

Canonical stress-energy structure:
- Canonical tensor form:
  `T^{mu nu}_can = (d^mu phi)(d^nu phi) - eta^{mu nu} L_scalar`.
- Symmetric bounded-report tensor (minimal scalar route):
  `T^{mu nu}_sym = (d^mu phi)(d^nu phi) - 1/2 eta^{mu nu}[(d_alpha phi)(d^alpha phi) - m_eff^2 phi^2 - 2V_int(phi)]`.
- Energy density component used for bounded interpretation:
  `T^{00} = 1/2[(partial_t phi)^2 + |grad phi|^2 + m_eff^2 phi^2] + V_int(phi)`.

Assumptions:
1. Lorentzian flat metric for this phase surface (`eta_mu_nu`).
2. Sufficient smoothness and boundary decay for integration-by-parts manipulations.
3. Bounded interaction potential where referenced.

Reproducibility pointers:
- `formal/output/toe_qft_scalar_stress_energy_artifact_v0.json`
- `formal/python/tests/test_toe_qft_scalar_covariance_gate.py`

Non-claim boundary:
- This report does not claim interacting renormalization completeness.
- This report does not claim quantization completion.
- This report does not claim gauge-field emergence or Standard Model embedding.
