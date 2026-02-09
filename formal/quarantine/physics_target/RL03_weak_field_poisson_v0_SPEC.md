# RL03 Weak-Field Poisson Limit Spec v0 (Scaffold)

Spec ID:
- COMP-RL-03/v0

Purpose:
- Scaffold a weak-field correspondence lane that targets a Poisson-type elliptic constraint.
- Governance-only scaffold; no implementation or physics claim yet.

Claim boundary:
- This lane asserts only a bounded correspondence under stated approximations.
- It does not claim GR recovery, Einstein equations, or real-world gravity identification.

Target contract (v0):
- Poisson form: nabla^2 Phi = kappa * rho
- kappa is a pinned scaling constant for this lane.
- Gauge: mean(Phi) = 0 for periodic domains.

Scope (design-only):
- Define a comparator surface for a scalar potential-like observable Phi.
- Use a pinned synthetic density profile rho(x) with deterministic boundary conditions.
- Require representation-eligible channels only (factor-through `.val`).

Planned evidence:
- Comparator module and deterministic front door (Python).
- Tests for deterministic execution and front-door contract.
- State doc entry with pinned evidence paths.

Failure modes (v0 intent):
- Poisson residual exceeds pinned tolerance.
- Domain parameters or gauge constraints are inconsistent.
- Artifact determinism checks fail.

Notes:
- Lane is blocked from promotion until non-alias equivalence is discharged.
