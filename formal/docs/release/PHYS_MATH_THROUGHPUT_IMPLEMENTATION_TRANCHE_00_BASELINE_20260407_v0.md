# PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_00_BASELINE_20260407_v0

## Tranche name
PHYS_MATH_THROUGHPUT_T00_BASELINE_CAPTURE

## Objective
Execute a bounded Phase 0 baseline capture for governance-vs-science signal mix without changing theorem surfaces, status semantics, or release-gate policy.

## Allowed files
- formal/python/tools/physics_math_throughput_baseline_snapshot.py (new)
- formal/docs/release/PHYS_MATH_THROUGHPUT_REMEDIATION_PROGRAM_v0.md (new)
- formal/docs/release/PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_00_BASELINE_20260407_v0.md (new)
- formal/output/reports/physics_math_throughput_baseline_20260407_v0.json (new)
- formal/python/tests/test_physics_math_throughput_baseline_snapshot_gate.py (new)

## Out of scope
- theorem-body edits in Lean surfaces
- status downgrades/upgrades
- governance suite lane split
- release-gate contract edits
- packet hold/freeze policy changes

## Acceptance
1. Baseline tool runs successfully.
2. Baseline artifact is generated and schema-valid.
3. Baseline gate is green.

## Rollback anchor
WORKING_TREE_BASELINE_20260407
