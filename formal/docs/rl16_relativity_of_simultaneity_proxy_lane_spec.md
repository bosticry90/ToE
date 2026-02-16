# RL16 Relativity of Simultaneity Proxy Lane Spec v0

Scope
- RL16 targets a relativity-of-simultaneity proxy in a pinned discrete setting.
- This lane is a simultaneity-offset proxy only.
- Positive control uses Lorentz simultaneity shift and should satisfy the pinned offset.
- Negative control uses a Galilean (no shift) proxy and should violate the offset.
- No external truth claim is made beyond the pinned discrete setting.

Pinned parameters
- c=1.0
- beta=0.6
- gamma=1/sqrt(1-beta^2)
- delta_t=0.2
- delta_x=1.5

Pinned observable
- delta_t_prime = gamma*(delta_t - beta*delta_x/c)
- simultaneity_residual = |delta_t_prime - expected_delta_t_prime|

Pinned pass criteria (expectation-aware)
- positive control: simultaneity_residual <= eps_simultaneity
- negative control: simultaneity_residual >= eps_break

Pinned tolerances
- eps_simultaneity=1e-8
- eps_break=1e-3

Comparator posture
- expectation-aware pass semantics per case kind
- comparisons are bounded to the pinned discrete report schema
