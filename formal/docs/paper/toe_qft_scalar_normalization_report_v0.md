# ToE QFT Scalar Normalization Report v0

Report ID:
- `toe_qft_scalar_normalization_report_v0`

Scope:
- Tranche G bounded free-scalar normalization and one-particle-state hardening for Route A.
- Keep explicit free-field posture and avoid interactions, gauge expansion, and scattering claims.

Input anchors:
- `formal/docs/paper/toe_qft_scalar_mode_expansion_report_v0.md`
- `formal/output/toe_qft_scalar_creation_annihilation_artifact_v0.json`
- `formal/docs/paper/toe_qft_scalar_operator_commutator_report_v0.md`

Normalization hardening:
1. Mode normalization statement (bounded):
- Use relativistic normalization compatible with the existing mode expansion.
- Ladder-operator normalization remains route-consistent with
  `[a_k, a_q^dagger] = (2pi)^3 delta^3(k-q)`.

2. Vacuum and one-particle-state construction (bounded):
- Vacuum posture: `a_k |0> = 0` for all admissible modes `k`.
- One-particle state definition: `|k> = a_k^dagger |0>`.
- Bounded norm statement: `<k|q> = (2pi)^3 delta^3(k-q)` under the same normalization convention.

3. Hamiltonian-facing interpretation (bounded):
- In free-scalar posture, `a_k^dagger a_k` is interpreted as occupation counting density contribution per mode.
- Full spectral-domain and interacting completion remains deferred.

Assumptions:
1. Free-scalar bounded regime only.
2. Distribution and smearing posture inherited from Tranches E-F.
3. Multi-particle scattering completion remains deferred.

Reproducibility pointers:
- `formal/output/toe_qft_scalar_one_particle_state_artifact_v0.json`
- `formal/python/tests/test_toe_qft_scalar_normalization_gate.py`

Non-claim boundary:
- This report does not claim interacting-field renormalization completion.
- This report does not claim gauge-sector quantization completion.
- This report does not claim multi-particle scattering completion.
- This report does not claim Standard Model spectrum completion.
