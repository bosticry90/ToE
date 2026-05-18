# v0.1-alpha dependency remediation tranche 001 documentation

## Scope

- Selected finding: `V01-ALPHA-DEP-REM-001`
- Selected tranche: `V01-ALPHA-DEP-REM-TRANCHE-001`
- Selected dependency: `master_action_stationary_implies_free_scalar_kg`
- Policy classification: `policy_acceptable_with_documentation_requirement`
- Documentation purpose: record the standard Lean axiom posture required by the v0.1-alpha release-policy adjudication result review.

## Accepted Lean Dependency Posture

- Accepted Lean dependencies: `[propext, Classical.choice, Quot.sound]`
- Project-local axioms used: `project_axioms_used = []`
- Project-local axiom count: `0`
- Lean evidence command: `#print axioms ToeFormal.QFT.FreeScalarDerivation.master_action_stationary_implies_free_scalar_kg`

The dependency posture is acceptable for v0.1-alpha because the only recorded axioms are standard Lean/mathlib axiomatic dependencies and no project-local axioms are present. This documentation records that posture for the selected dependency only.

## What This Documentation Does Not Prove

- It does not prove `master_action_stationary_implies_free_scalar_kg`.
- It does not discharge Lean theorem debt or proof debt.
- It does not discharge retained assumptions.
- It does not clear `V01-ALPHA-DEP-REM-001` by itself.
- It does not assemble the v0.1-alpha release packet or mark release readiness.
- It does not authorize Phase 2, seam closure, empirical validation, or master-action promotion.

## Policy Rationale

The standard Lean axioms propext, Classical.choice, and Quot.sound are acceptable for the v0.1-alpha dependency posture of the selected theorem when no project-local axioms are used, provided the release materials document this standard-axiom posture.

A later result-review or release-policy follow-up must record that tranche 001 depends only on standard Lean axioms [propext, Classical.choice, Quot.sound] and no project-local axioms before the blocker can be downgraded.

Project-local axioms remain absent because the accepted evidence records `project_axioms_used = []` and `project_axiom_count = 0`. Any later change to that evidence requires a separate review surface.

## Blocker Movement Boundary

Blocker movement still requires result review of this documentation packet. This documentation packet prepares the evidence surface only; it does not downgrade, clear, or otherwise move the blocker.

## Other Release-Blocking Obligations

- `V01-ALPHA-DEP-REM-002` / `stationary_implies_operator_zero`: tracked_unmodified_not_executed_in_tranche_001
- `V01-ALPHA-DEP-REM-003` / `finite_transport_theorems_construct_residual_package_v0`: tracked_unmodified_not_executed_in_tranche_001
- `V01-ALPHA-DEP-REM-004` / `qft_gr_source_map_eligibility_ladder_summary_source_map_not_authorized_v0`: tracked_unmodified_not_executed_in_tranche_001
- `V01-ALPHA-DEP-REM-005` / `supplied_interface_alignment_semantics_construct_bridge_package_v0`: tracked_unmodified_not_executed_in_tranche_001
- `V01-ALPHA-DEP-REM-006` / `supplied_alignment_constructs_sr_cosmo_regime_transport_package_v0`: tracked_unmodified_not_executed_in_tranche_001
