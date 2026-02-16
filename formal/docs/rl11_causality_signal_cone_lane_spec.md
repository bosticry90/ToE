# RL11 Causality / Signal-Cone Lane Spec v0

Scope
- RL11 targets a causality (domain-of-dependence) admissibility proxy in a pinned 1D update rule.
- Positive control enforces a CFL-like bound and should respect a signal-cone bound.
- Negative control violates the CFL bound and should show superluminal leakage outside the cone.
- No external truth claim is made beyond the pinned discrete setting.

Pinned system (1D grid)
- Domain length: L=6.283185307179586
- Grid points: N=256
- Spacing: dx=L/N
- Reference speed: c0=1.0
- CFL_max=1.0

Positive control (causal)
- Local hyperbolic update rule on the 1D grid.
- Timestep: dt_pos=0.01
- CFL: c0*dt_pos/dx <= CFL_max

Negative control (acausal)
- Same local update rule, but CFL violation.
- Timestep: dt_neg=0.05
- CFL: c0*dt_neg/dx > CFL_max

Pinned observable
- leakage_outside_cone: integrated |psi|^2 mass outside the predicted signal-cone.
- signal-cone / domain-of-dependence is defined by |x - x0| <= c0 * t.

Pinned pass criteria (expectation-aware)
- positive control: leakage_outside_cone <= eps_causal
- negative control: leakage_outside_cone >= eps_acausal

Pinned tolerances
- eps_causal=1e-10
- eps_acausal=1e-3

Comparator posture
- expectation-aware pass semantics per case kind
- comparisons are bounded to the pinned discrete report schema
