# Sandbox Promotion Migration Phase2-Phase6 Declaration 2026-04-19 v0

## Tranche name

- Phase 2 completion and Phase 6 bounded audit kickoff for the sandbox-first promotion-gated governance migration.

## Objective

- Declare one governed promotion-review wrapper for the already bound COSMO-SR Cycle07 pilot.
- Pin the canonical mutation protocol that a `promote` decision must emit.
- Execute one bounded sandbox to promotion-lane review cycle and record the governed outcome without fabricating a canonical promotion.

## Allowed files

- formal/docs/release/SANDBOX_PROMOTION_MIGRATION_PHASE2_PHASE6_DECLARATION_20260419_v0.md (new)
- formal/docs/release/SANDBOX_PROMOTION_GOVERNED_REVIEW_WRAPPER_COSMO_SR_CYCLE07_20260419_v0.json (new)
- formal/docs/release/SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_20260419_v0.md (new)
- formal/output/reports/sandbox_promotion_cosmo_sr_cycle07_payload_record_20260419_v0.json (new)
- formal/python/tools/sandbox_promotion_governed_review_wrapper_cosmo_sr_cycle07_report.py (new)
- formal/output/reports/sandbox_promotion_governed_review_wrapper_cosmo_sr_cycle07_20260419_v0.json (new)
- formal/python/tests/test_sandbox_promotion_governed_review_wrapper_cosmo_sr_cycle07_report.py (new)
- formal/docs/release/PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0.md
- formal/python/tests/test_sandbox_promotion_lane_policy_gate.py
- formal/python/tests/test_sandbox_promotion_phase2_phase4_contract_gate.py
- formal/python/tests/test_sandbox_promotion_migration_phase0_baseline_gate.py
- State_of_the_Theory.md
- formal/docs/paper/PHYSICS_ROADMAP_v0.md

## Out of scope

- Authority-ownership cutover beyond the bounded pilot wrapper.
- Widening the promotion lane beyond `ROW-SEAM-COSMO-SR-001` / `SEAM-COSMO-SR`.
- Any canonical promotion that is not explicitly emitted by the governed review wrapper.

## Acceptance

- Governed review wrapper declaration exists and binds the COSMO-SR Cycle07 pilot to the payload, pilot-binding, and mutation-protocol surfaces.
- Canonical mutation protocol exists and fail-closes `promote` when surface deltas, pre/post state, or rollback anchors are missing.
- A schema-compliant payload record exists for the current COSMO-SR Cycle07 sandbox artifact.
- A governed review report is materialized from current repo evidence and lands on an honest terminal outcome.
- Mirrors and focused gates are updated to reflect Phase 2 completion and Phase 6 execution.

## Rollback anchor

- formal/docs/release/SANDBOX_PROMOTION_MIGRATION_PHASE2_PHASE4_DECLARATION_20260419_v0.md
- formal/docs/release/SANDBOX_ARTIFACT_CLASSIFICATION_METADATA_SCHEMA_20260419_v0.md
- formal/docs/release/SANDBOX_PROMOTION_PAYLOAD_REQUIREMENTS_20260419_v0.md
- formal/docs/release/SANDBOX_PROMOTION_BOUNDED_PILOT_BINDING_COSMO_SR_CYCLE07_20260419_v0.json

## Hard stop rule

- Stop immediately if the wrapper requires widening beyond one bounded pilot, if the mutation protocol implies unspecific canonical writeback, or if the current COSMO-SR artifact is represented as promoted despite `NOT_YET_DISCHARGED` evidence.

## Boundary freshness note

- This tranche is repository-local and non-claim.
- The expected live governed outcome for the current pilot may be `hold`; the tranche is still valid if the wrapper and audit are executed honestly and fail closed.