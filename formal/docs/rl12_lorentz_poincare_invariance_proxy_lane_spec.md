# RL12 Lorentz/Poincare Invariance Proxy Lane Spec v0

Scope
- RL12 targets a Lorentz/Poincare invariance proxy in a pinned discrete setting.
- Positive control applies a consistent boost transform and should preserve the invariant metric.
- Negative control applies an inconsistent transform and should break the invariant metric.
- No external truth claim is made beyond the pinned discrete setting.

Pinned system (1D grid)
- Domain length: L=6.283185307179586
- Time window: T=3.141592653589793
- Grid points: Nx=256, Nt=128
- Spacing: dx=L/Nx, dt=T/Nt

Pinned transform (boost)
- c=1.0
- beta=0.3
- gamma=1/sqrt(1-beta^2)
- Boost map: x' = gamma * (x - beta * c * t)
- Boost map: t' = gamma * (t - beta * x / c)

Pinned observable
- invariant_metric: L2 difference between the field evaluated in (x,t) and the boosted field in (x',t').

Pinned pass criteria (expectation-aware)
- positive control: invariant_metric <= eps_invariant
- negative control: invariant_metric >= eps_break

Pinned tolerances
- eps_invariant=1e-8
- eps_break=1e-3

Comparator posture
- expectation-aware pass semantics per case kind
- comparisons are bounded to the pinned discrete report schema
