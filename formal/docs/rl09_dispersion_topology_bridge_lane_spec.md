# RL09 Dispersion-Topology Bridge Lane Spec v0

Scope
- RL09 targets a dispersion-topology bridge in a pinned 1D two-band model.
- The topology signal is the winding of the Bloch d-vector around the origin.
- Positive and negative controls are expectation-aware and deterministic.
- No external truth claim is made beyond the pinned discrete setting.

Pinned model
- H(k) = d_x(k) * sigma_x + d_y(k) * sigma_y
- d_x(k) = t1 + t2 * cos(k)
- d_y(k) = t2 * sin(k)
- k grid: N_k=256 on [0, L) with L=6.283185307179586

Pinned controls
- positive control: t1=0.5, t2=1.0, expected winding W=1
- negative control: t1=1.0, t2=0.5, expected winding W=0

Pinned diagnostics
- W: winding of (d_x, d_y)
- eps_winding=1e-8

Pinned pass criteria
- positive control: abs(W - 1) <= eps_winding
- negative control: abs(W - 0) <= eps_winding

Artifacts (planned)
- reference_report.json: pinned params + W + optional min gap
- candidate_report.json: same schema and diagnostics

Comparator posture
- expectation-aware pass semantics per case kind
- comparisons are bounded to the pinned discrete report schema
