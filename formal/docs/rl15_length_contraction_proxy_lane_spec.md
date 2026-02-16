# RL15 Length Contraction Proxy Lane Spec v0

Scope
- RL15 targets a Lorentz length-contraction proxy in a pinned discrete setting.
- This lane is a length contraction proxy only.
- Positive control uses Lorentz contraction and should satisfy the pinned ratio.
- Negative control uses a Galilean (no contraction) proxy and should violate the ratio.
- No external truth claim is made beyond the pinned discrete setting.

Pinned parameters
- c=1.0
- beta=0.6
- gamma=1/sqrt(1-beta^2)
- L0=2.0

Pinned observable
- contraction_ratio = L/L0
- contraction_residual = |contraction_ratio - 1/gamma|

Pinned pass criteria (expectation-aware)
- positive control: contraction_residual <= eps_contraction
- negative control: contraction_residual >= eps_break

Pinned tolerances
- eps_contraction=1e-8
- eps_break=1e-3

Comparator posture
- expectation-aware pass semantics per case kind
- comparisons are bounded to the pinned discrete report schema
