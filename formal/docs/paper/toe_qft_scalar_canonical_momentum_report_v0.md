# ToE QFT Scalar Canonical Momentum Report v0

Report ID:
- `toe_qft_scalar_canonical_momentum_report_v0`

Scope:
- Tranche D bounded refinement of Route A quantization.
- Sharpen canonical momentum and Hamiltonian statements for the scalar lane.

Input anchors:
- `formal/docs/paper/toe_qft_scalar_canonical_quantization_report_v0.md`
- `formal/docs/paper/toe_qft_scalar_covariance_report_v0.md`
- `formal/output/toe_qft_scalar_canonical_quantization_artifact_v0.json`

Canonical momentum definition:
- Starting from scalar density
  `L_scalar = 1/2 (partial_t phi)^2 - 1/2 |grad phi|^2 - 1/2 m_eff^2 phi^2 - V_int(phi)`.
- Canonical momentum is
  `pi(x) = dL_scalar / d(partial_t phi) = partial_t phi`.

Hamiltonian density refinement:
- Legendre transform relation:
  `H = pi partial_t phi - L_scalar`.
- Substituting canonical momentum gives
  `H = 1/2 pi^2 + 1/2 |grad phi|^2 + 1/2 m_eff^2 phi^2 + V_int(phi)`.

Operator-facing bounded interpretation:
- Canonical pair `(phi, pi)` is treated as operator-valued distributions under a bounded equal-time route contract.
- Route-facing commutator structure remains:
  `[phi(t,x), pi(t,y)] = i delta^3(x-y)`,
  `[phi,phi] = 0`,
  `[pi,pi] = 0`.

Assumptions:
1. Equal-time foliation is admissible in the bounded route context.
2. Distribution pairing is used for operator-valued field interpretation.
3. Regularization and domain closure remain deferred to later hardening tranches.

Reproducibility pointers:
- `formal/output/toe_qft_scalar_hamiltonian_density_artifact_v0.json`
- `formal/python/tests/test_toe_qft_scalar_hamiltonian_gate.py`

Non-claim boundary:
- This report does not claim interacting renormalization completion.
- This report does not claim full operator-domain closure.
- This report does not claim gauge emergence or Standard Model embedding.
