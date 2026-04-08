# PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_01_RETRO_TRUTH_ALIGNMENT_20260407_v0

## Tranche name
PHYS_MATH_THROUGHPUT_T01_RETRO_TRUTH_ALIGNMENT_PREP

## Objective
Declare a bounded Phase 1 retroactive truth-alignment prep slice that exposes selective downgrade candidates and proof-debt bindings without executing status mutations.

## Allowed files
- formal/docs/release/PHYS_MATH_THROUGHPUT_REMEDIATION_PROGRAM_v0.md (edit)
- formal/docs/release/PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_01_RETRO_TRUTH_ALIGNMENT_20260407_v0.md (new)
- formal/output/reports/physics_math_throughput_phase1_retro_truth_alignment_20260407_v0.json (new)
- formal/python/tests/test_physics_math_throughput_phase1_retro_truth_alignment_gate.py (new)

## Out of scope
- theorem-body edits in Lean surfaces
- status downgrades/upgrades in authority surfaces
- release-gate contract edits
- non-claim boundary edits
- packet hold/freeze policy edits

## Acceptance
1. Phase 1 checkpoint artifact exists and is schema-valid.
2. Candidate downgrade set is explicit and bounded.
3. All candidate rows include debt or evidence pointer fields.
4. Status mutation remains not executed in tranche 01.

## Rollback anchor
WORKING_TREE_BASELINE_20260407
