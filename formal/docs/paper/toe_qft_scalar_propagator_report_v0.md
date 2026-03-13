# ToE QFT Scalar Propagator Report v0

Report ID:
- `toe_qft_scalar_propagator_report_v0`

Scope:
- Tranche I bounded free-scalar propagator and two-point-function hardening for Route A.
- Stay within the pinned free-scalar lane and avoid interaction, gauge, and renormalization over-claims.

Input anchors:
- `formal/docs/paper/toe_qft_scalar_mode_expansion_report_v0.md`
- `formal/docs/paper/toe_qft_scalar_normalization_report_v0.md`
- `formal/docs/paper/toe_qft_scalar_operator_commutator_report_v0.md`
- `formal/output/toe_qft_scalar_creation_annihilation_artifact_v0.json`
- `formal/output/toe_qft_scalar_one_particle_state_artifact_v0.json`

Propagator and two-point hardening:
1. Vacuum two-point function (bounded free-scalar route):
- Wightman-facing two-point structure is pinned as
  `W(x-y) = <0| phi(x) phi(y) |0>`.
- Equal-time commutator and mode-normalization inputs fix the free-field two-point kernel posture.

2. Time-ordered two-point function:
- Feynman propagator surface is pinned as
  `Delta_F(x-y) = <0| T{phi(x) phi(y)} |0>`.
- In momentum-space bounded free-field form:
  `Delta_F(k) = i / (k^2 - m^2 + i epsilon)`.

3. Equation-of-motion consistency:
- Propagator route is pinned to the free Klein-Gordon operator contract:
  `(box + m^2) Delta_F(x-y) = -i delta^4(x-y)`
  under the declared distribution posture.

4. Existing route compatibility:
- Two-point/propagator surface is consistent with prior canonical commutator, mode expansion, and one-particle normalization tranches.
- This tranche upgrades physics weight within the same bounded lane rather than broadening scope.

Assumptions:
1. Free-scalar regime only (`V_int` omitted for this tranche).
2. Distribution-smearing posture remains in force for operator products.
3. Domain closure and interacting renormalization remain deferred.

Reproducibility pointers:
- `formal/output/toe_qft_scalar_two_point_function_artifact_v0.json`
- `formal/python/tests/test_toe_qft_scalar_propagator_gate.py`

Non-claim boundary:
- This report does not claim interacting-field completion.
- This report does not claim gauge-sector completion.
- This report does not claim renormalization completion.
- This report does not claim multi-particle scattering completion.
