# CX-01 Update Contractivity Lane Spec v0

Scope
- CX-01 is a stability-family admissibility lane.
- It checks whether a pinned update rule is contractive under a pinned norm.
- This lane is internal and bounded; no external truth claim is made.

Pinned constraint
- Constraint: contractive admissibility bound `L <= 1` where `L` is empirical Lipschitz ratio.
- Positive control uses `k_contract < 1`.
- Negative control uses `k_break > 1`.

Controls (expectation-aware)
- positive control: linear update with per-step factor `k_contract=0.8`, steps=3.
- negative control: same update family with `k_break=1.05`, steps=3.

Pinned pass criteria
- positive control: `empirical_lipschitz <= 1 + eps_contractivity`.
- negative control: explicit break detection (`empirical_lipschitz > 1 + eps_break`).

Pinned tolerances
- `eps_contractivity=1e-8`
- `eps_break=1e-3`

Comparator posture
- expectation-aware pass semantics per case kind
- comparisons are bounded to the pinned CX-01 report schema
- active comparator profile must match artifact-declared eps parameters
