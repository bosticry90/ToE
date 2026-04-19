# Sandbox Promotion Migration Phase3 Implementation 2026-04-19 v0

## Tranche name

- Phase 3 authority-owner matrix and fail-closed cutover gate implementation for the sandbox-first promotion-gated governance migration.

## Objective

- Pin the authority-owner matrix for the two-lane sandbox-promotion architecture.
- Fail close on mixed authority residency between sandbox-only surfaces and promotion/canonical mutation surfaces.
- Use the Phase 3 hardening slice to strengthen the broader Phase 5 boundary-enforcement family.

## Allowed files

- formal/docs/release/SANDBOX_PROMOTION_MIGRATION_PHASE3_IMPLEMENTATION_20260419_v0.md (new)
- formal/docs/release/SANDBOX_PROMOTION_AUTHORITY_OWNERSHIP_MATRIX_20260419_v0.md (new)
- formal/docs/release/SANDBOX_PHYSICS_LANE_EXECUTION_POLICY_20260418_v0.md
- formal/docs/release/PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0.md
- formal/python/tests/test_sandbox_promotion_authority_ownership_cutover_gate.py (new)
- formal/python/tests/test_sandbox_promotion_lane_policy_gate.py
- formal/python/tests/test_sandbox_promotion_phase2_phase4_contract_gate.py
- formal/python/tests/test_sandbox_promotion_migration_phase0_baseline_gate.py
- formal/python/tests/test_sandbox_promotion_post_pilot_decision_phase3_followthrough_gate.py
- State_of_the_Theory.md
- formal/docs/paper/PHYSICS_ROADMAP_v0.md

## Out of scope

- Widening the bounded pilot.
- Retiring the pilot or promotion lane.
- Adding the full remaining Phase 5 enforcement family beyond the cutover baseline.

## Acceptance

- Authority-owner matrix exists with explicit canonical owners, parity surfaces, and enforcing gate pointers.
- Sandbox and promotion lane policies bind to the matrix and the new cutover gate.
- Focused gate passes and mirrors record Phase 3 as objectively complete.
- Phase 5 remains partial but explicitly strengthened by the cutover baseline.

## Rollback anchor

- formal/docs/release/SANDBOX_PROMOTION_MIGRATION_PHASE3_AUTHORITY_OWNERSHIP_HARDENING_DECLARATION_20260419_v0.md
- formal/output/reports/sandbox_promotion_post_pilot_decision_cosmo_sr_cycle07_20260419_v0.json

## Hard stop rule

- Stop immediately if the matrix allows sandbox surfaces to own canonical mutation authority, if the cutover gate allows mixed authority residency, or if unrelated lane widening is introduced.

## Boundary freshness note

- This tranche completes the bounded Phase 3 authority-hardening objective only.
- This tranche does not claim the full Phase 5 enforcement family is complete.