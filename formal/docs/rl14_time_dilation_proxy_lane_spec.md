# RL14 Time Dilation Proxy Lane Spec v0

Scope
- RL14 targets a Lorentz time-dilation proxy in a pinned discrete setting.
- This lane is a time dilation proxy only.
- Positive control uses Lorentz dilation and should satisfy the pinned ratio.
- Negative control uses a Galilean (no dilation) proxy and should violate the ratio.
- No external truth claim is made beyond the pinned discrete setting.

Pinned parameters
- c=1.0
- beta=0.6
- gamma=1/sqrt(1-beta^2)
- delta_t=2.0

Pinned observable
- dilation_ratio = delta_tau/delta_t
- dilation_residual = |dilation_ratio - 1/gamma|

Pinned pass criteria (expectation-aware)
- positive control: dilation_residual <= eps_dilation
- negative control: dilation_residual >= eps_break

Pinned tolerances
- eps_dilation=1e-8
- eps_break=1e-3

Comparator posture
- expectation-aware pass semantics per case kind
- comparisons are bounded to the pinned discrete report schema
