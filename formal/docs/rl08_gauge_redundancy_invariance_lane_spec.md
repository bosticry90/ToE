# RL08 Gauge Redundancy Invariance Lane Spec v0

Scope
- RL08 targets gauge redundancy invariance in a discrete, pinned setting.
- positive control validates gauge-invariant observables remain unchanged under a gauge transform.
- negative control introduces a gauge-breaking perturbation and must fail invariance.
- No external truth claim is made beyond the pinned discrete setting.

Pinned system (baseline)
- Domain: 1D periodic ring, length L=6.283185307179586
- Grid: N=128, dx=L/N
- Field: complex scalar psi(x)
- Gauge transform: psi(x) -> psi(x) * exp(i*phi(x)) with pinned phi(x)=alpha*sin(x)
- alpha=0.2 (pinned)

Pinned observable
- Observable: |psi(x)|^2 (gauge invariant)
- Invariance residual: max | |psi|^2 - |psi_g|^2 |
- tolerance: eps_invariant=1e-10

Negative control (gauge breaking)
- Breaker: use observable Re(psi) instead of |psi|^2
- Expected: invariance residual exceeds eps_break
- eps_break=1e-3

Pinned pass criteria
- Positive control pass: invariance residual <= eps_invariant
- Negative control pass: invariance residual >= eps_break

Artifacts (planned)
- reference_report.json: pinned params + invariance residuals (positive, negative)
- candidate_report.json: same schema and diagnostics

Comparator posture
- expectation-aware pass semantics per case kind
- comparisons are bounded to the pinned discrete report schema
