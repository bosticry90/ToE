# CT-04 Minimality No-Go Lane Spec v0

Scope
- CT-04 is a minimality/no-go conditional theorem lane.
- It tests whether removing a pinned admissibility constraint makes the target unattainable.
- This lane is internal and bounded; no external truth claim is made.

Pinned constraint
- Constraint: CFL bound (cfl_max) enforced under CT-02/CT-03.
- Minimality toggle: constraint_removed = cfl_bound.

Controls (expectation-aware)
- positive control: baseline update with cfl <= cfl_max.
- negative control: update with cfl > cfl_max (constraint removed).

Pinned pass criteria
- positive control: energy drift <= eps_drift and cfl <= cfl_max.
- negative control: cfl > cfl_max (violation detected).

Pinned tolerances
- eps_drift=5e-3
- eps_break=1e-3

Comparator posture
- expectation-aware pass semantics per case kind
- comparisons are bounded to the pinned discrete report schema
