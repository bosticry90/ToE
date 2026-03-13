# ToE QFT Scalar Nonrelativistic Limit Report v0

Report ID:
- `toe_qft_scalar_nonrelativistic_limit_report_v0`

Scope:
- Tranche H bounded non-relativistic bridge for the free-scalar Route A lane.
- Derive a Schrodinger-class limit under explicit low-energy assumptions.

Input anchors:
- `formal/docs/paper/toe_qft_scalar_mode_expansion_report_v0.md`
- `formal/docs/paper/toe_qft_scalar_normalization_report_v0.md`
- `formal/output/toe_qft_scalar_one_particle_state_artifact_v0.json`

Non-relativistic bridge hardening:
1. Low-energy assumptions (bounded):
- Momentum scale obeys `|k| << m` with `c=1` convention.
- Positive-frequency sector is selected for the bounded one-particle interpretation.

2. Phase extraction and envelope field:
- Write `phi(t,x) = exp(-i m t) psi(t,x) / sqrt(2m)` plus suppressed fast-oscillating remainder terms.
- Retain leading-order slow-envelope dynamics for `psi` in the low-energy regime.

3. Schrodinger-class limit statement (bounded):
- At leading order in `|k|/m`, envelope dynamics satisfy
  `i partial_t psi = -(nabla^2/(2m)) psi`.
- This bridges the free-scalar operator route to a bounded Schrodinger-class one-particle regime.

Assumptions:
1. Free-scalar bounded regime only.
2. Non-relativistic expansion controlled to leading order.
3. Multi-particle scattering and interaction corrections remain deferred.

Reproducibility pointers:
- `formal/output/toe_qft_scalar_schrodinger_limit_artifact_v0.json`
- `formal/python/tests/test_toe_qft_scalar_nonrelativistic_limit_gate.py`

Non-claim boundary:
- This report does not claim interacting-field non-relativistic completion.
- This report does not claim gauge-coupled Schrodinger limits.
- This report does not claim multi-particle scattering completion.
- This report does not claim Standard Model low-energy completion.
