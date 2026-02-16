# Claim Taxonomy v0

Purpose
- Provide a canonical paper-facing label system so every statement is auditable.
- Prevent claim drift across theorem, policy, and empirical surfaces.

Labels (canonical strings)
- `T-PROVED`: Lean theorem with no undisclosed assumptions beyond imported theorem context.
- `T-CONDITIONAL`: Lean theorem proved under explicit assumption predicates that are listed in the statement.
- `E-REPRO`: Deterministic computational result with pinned artifacts and lock equality checks.
- `P-POLICY`: Declared governance/admissibility principle (not a theorem-level discharge).
- `B-BLOCKED`: Explicitly not yet discharged within current toolchain/scope; no claim upgrade permitted.

Paper-facing rules
- Every claim in the paper must carry exactly one taxonomy label.
- Every labeled claim must include a concrete evidence pointer (Lean module/theorem or lock path).
- Conditional claims must list full assumption surfaces.
- Policy claims must explicitly state they are not theorem-level.
- Blocked items must include non-claim language and a promotion condition.

Solver-elimination promotion rule (Track B, v0)
- Solver-grade rows may be promoted from `T-CONDITIONAL` to `T-PROVED` when the theorem statement:
  - eliminates explicit candidate-field theorem input (`Φ` is not an input binder), and
  - exposes existential output (`∃ Φ` or `∃! Φ`) under explicit solver assumptions.
- This promotion is contract-level only and does not by itself upgrade blocker gate `TOE-GR-3D-03`.

Publication-grade derivation gate rule (all pillars, v0 policy)
- `T-PROVED` is necessary but not sufficient for publication-grade derivation claims.
- publication-grade promotion additionally requires closure of `DERIVATION_COMPLETENESS_GATE`:
  - `formal/docs/paper/DERIVATION_COMPLETENESS_GATE_v0.md`
  - target ID `TARGET-GR01-DERIV-COMPLETENESS-GATE-PLAN` (GR01 first implementation).
- Gate closure requires all four layers:
  - analytic discharge completeness,
  - mainstream equivalence proof,
  - assumption minimization audit,
  - literature alignment mapping.
