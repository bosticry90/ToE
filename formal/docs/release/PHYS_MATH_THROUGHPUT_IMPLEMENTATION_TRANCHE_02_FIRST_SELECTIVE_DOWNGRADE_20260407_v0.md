# PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_02_FIRST_SELECTIVE_DOWNGRADE_20260407_v0

## Tranche name
PHYS_MATH_THROUGHPUT_T02_FIRST_SELECTIVE_DOWNGRADE_EXECUTION

## Objective
Execute the first bounded selective downgrade package from the phase1 candidate set while preserving release-gate truth and non-claim boundaries.

## Allowed files
- formal/docs/release/PHYS_MATH_THROUGHPUT_REMEDIATION_PROGRAM_v0.md (edit)
- formal/docs/release/PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_02_FIRST_SELECTIVE_DOWNGRADE_20260407_v0.md (new)
- formal/output/reports/physics_math_throughput_phase1_t02_selective_downgrade_execution_20260407_v0.json (new)
- formal/python/tests/test_physics_math_throughput_phase1_t02_selective_downgrade_execution_gate.py (new)

## Out of scope
- theorem-body edits in Lean surfaces
- release-gate contract edits
- packet or scalar freeze policy edits
- broad multi-surface status rewrites

## Execution slice
1. Execute exactly one candidate from the tranche-01 candidate set.
2. Bind the executed row to explicit debt/evidence pointer.
3. Declare re-upgrade criteria as explicit gates plus evidence conditions.

## Acceptance
1. Tranche 02 checkpoint artifact exists and is schema-valid.
2. Exactly one candidate row is marked as executed.
3. Executed row includes debt binding and re-upgrade criteria.
4. Tranche 02 gate is green.

## Rollback anchor
WORKING_TREE_BASELINE_20260407
