# Nonrelativistic Limit NLSE Comparator Lane (Scaffold)

Spec ID:
- COMP-NR-NLSE-01/v1

Purpose:
- Scaffold a physics-limit comparator lane that targets the nonrelativistic limit with Schrodinger/NLSE-form dynamics.
- Governance-only scaffold; no implementation or physics claim yet.

Scope (design-only):
- Define a comparator surface for nonrelativistic dispersion and conserved-quantity behavior.
- Declare the scaling assumptions that yield the Schrodinger/NLSE regime.
- Require representation-eligible channels only (factor-through `.val`).

Planned evidence:
- Comparator module and deterministic front door (Python).
- Tests for deterministic execution and front-door contract.
- State doc entry with pinned evidence paths.

Notes:
- Lane is blocked from promotion until non-alias equivalence is discharged.
