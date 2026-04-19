# Sandbox Promotion Migration Phase3 Authority Ownership Hardening Declaration 2026-04-19 v0

## Tranche name

- Phase 3 authority-ownership hardening and cutover opening tranche for the sandbox-first promotion-gated governance migration.

## Objective

- Open the bounded tranche that will harden authority ownership for the two-lane sandbox-promotion architecture.
- Pin authority-hardening as the next infrastructure implementation target after the bounded post-pilot decision is recorded.
- Prevent silent widening, mixed authority residency, or ambiguous ownership between sandbox and promotion surfaces.

## Allowed files

- formal/docs/release/SANDBOX_PROMOTION_MIGRATION_PHASE3_AUTHORITY_OWNERSHIP_HARDENING_DECLARATION_20260419_v0.md (new)
- State_of_the_Theory.md
- formal/docs/paper/PHYSICS_ROADMAP_v0.md
- formal/python/tests/test_sandbox_promotion_migration_phase0_baseline_gate.py
- formal/python/tests/test_sandbox_promotion_lane_policy_gate.py
- formal/python/tests/test_sandbox_promotion_post_pilot_decision_phase3_followthrough_gate.py

## Out of scope

- Completing authority-hardening implementation in this opening tranche.
- Introducing a new live cutover, widening the pilot, or retiring the pilot.
- Broadening the promotion lane beyond the bounded COSMO-SR Cycle07 path.

## Acceptance

- A formal Phase 3 declaration exists and is mirrored into the active authority surfaces.
- The mirrors record that Phase 3 is opened but still not objectively complete.
- The architecture next action points to implementing authority-ownership hardening rather than reopening pilot evaluation.

## Rollback anchor

- formal/docs/release/SANDBOX_PROMOTION_MIGRATION_PHASE2_PHASE6_DECLARATION_20260419_v0.md
- formal/output/reports/sandbox_promotion_governed_review_wrapper_cosmo_sr_cycle07_20260419_v0.json

## Hard stop rule

- Stop immediately if the declaration implies that authority hardening is already complete, if it widens the pilot before a separate declaration, or if it mutates canonical ownership surfaces outside the explicitly allowed scope.

## Boundary freshness note

- This tranche opens Phase 3 formally but does not complete it.
- This declaration is repository-local and non-claim.