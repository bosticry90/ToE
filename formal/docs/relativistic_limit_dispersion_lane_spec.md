# Relativistic Limit Dispersion Comparator Lane (Scaffold)

Spec ID:
- COMP-REL-DISP-01/v1

Purpose:
- Scaffold a physics-limit comparator lane that tests relativistic-form dispersion in a declared small-excitation regime.
- Governance-only scaffold; no implementation or physics claim yet.

Scope (design-only):
- Define a comparator surface for small-excitation dispersion.
- Declare the target relativistic form (or quantified deviation) in a pinned limit.
- Require representation-eligible channels only (factor-through `.val`).

Planned evidence:
- Comparator module and deterministic front door (Python).
- Tests for deterministic execution and front-door contract.
- State doc entry with pinned evidence paths.

Notes:
- This lane is blocked from promotion until the non-alias equivalence target is discharged.
