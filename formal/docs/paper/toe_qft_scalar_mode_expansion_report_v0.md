# ToE QFT Scalar Mode Expansion Report v0

Report ID:
- `toe_qft_scalar_mode_expansion_report_v0`

Scope:
- Tranche F bounded free-scalar mode-expansion and creation/annihilation operator hardening for Route A.
- Keep explicit free-field posture and avoid interaction/gauge broadening.

Input anchors:
- `formal/docs/paper/toe_qft_scalar_operator_commutator_report_v0.md`
- `formal/output/toe_qft_scalar_operator_commutator_artifact_v0.json`
- `formal/docs/paper/toe_qft_scalar_canonical_quantization_report_v0.md`

Mode expansion hardening:
1. Free-scalar field mode decomposition (bounded):
- `phi(t,x) = integral d^3k / ((2pi)^3 sqrt(2 omega_k)) [a_k e^{-i(omega_k t-k.x)} + a_k^dagger e^{+i(omega_k t-k.x)}]`
- `omega_k = sqrt(k^2 + m^2)` with `m^2 >= 0` in this bounded tranche.

2. Creation/annihilation operator interpretation:
- `a_k` lowers one-particle occupation in mode `k`.
- `a_k^dagger` raises one-particle occupation in mode `k`.
- Vacuum-facing posture is bounded to canonical free-field Fock interpretation.

3. Equal-time commutator compatibility (bounded):
- Mode expansion is route-consistent with
  `[a_k, a_q^dagger] = (2pi)^3 delta^3(k-q)` and vanishing `[a_k, a_q]`, `[a_k^dagger, a_q^dagger]`.
- This reproduces bounded equal-time canonical commutators from the previous tranche.

Assumptions:
1. Free-scalar bounded regime only.
2. Distribution and smearing posture inherited from Tranche E.
3. Full domain rigor and interacting completion remain deferred.

Reproducibility pointers:
- `formal/output/toe_qft_scalar_creation_annihilation_artifact_v0.json`
- `formal/python/tests/test_toe_qft_scalar_mode_expansion_gate.py`

Non-claim boundary:
- This report does not claim interacting-field renormalization completion.
- This report does not claim gauge-sector mode decomposition completion.
- This report does not claim Standard Model operator-spectrum completion.
