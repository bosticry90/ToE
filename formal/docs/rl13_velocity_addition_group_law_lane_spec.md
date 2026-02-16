# RL13 Velocity Addition Group-Law Lane Spec v0

Scope
- RL13 targets a Lorentz velocity-addition group-law proxy in a pinned 1D setting.
- Positive control uses Einstein addition and should satisfy composition consistency.
- Negative control uses Galilean addition and should violate composition consistency.
- No external truth claim is made beyond the pinned discrete setting.

Pinned parameters
- c=1.0
- beta_u=0.3
- beta_v=0.4
- gamma(u)=1/sqrt(1-beta_u^2)
- gamma(v)=1/sqrt(1-beta_v^2)

Pinned composition
- Einstein addition: beta_uv = (beta_u + beta_v)/(1 + beta_u*beta_v)
- Galilean addition: beta_uv_gal = beta_u + beta_v

Pinned observable
- addition_residual: |beta_comp - beta_uv|, where beta_comp is the composed velocity from two sequential boosts.

Pinned pass criteria (expectation-aware)
- positive control: addition_residual <= eps_addition
- negative control: addition_residual >= eps_break

Pinned tolerances
- eps_addition=1e-8
- eps_break=1e-3

Comparator posture
- expectation-aware pass semantics per case kind
- comparisons are bounded to the pinned discrete report schema
