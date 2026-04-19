# Sandbox Promotion Migration Phase 2 and Phase 4 Declaration (2026-04-19)

## Tranche name
SANDBOX_PROMOTION_MIGRATION_PHASE2_PHASE4_SCHEMA_PAYLOAD_AND_PILOT_BINDING

## Objective
Execute the bounded tranche that makes Phase 4 objective and advances Phase 2 by pinning the sandbox artifact classification schema, promotion payload requirements, and one bounded pilot-track binding before any governed promotion review wrapper is declared.

## Allowed files
- formal/docs/release/SANDBOX_PROMOTION_MIGRATION_PHASE2_PHASE4_DECLARATION_20260419_v0.md (new)
- formal/docs/release/SANDBOX_ARTIFACT_CLASSIFICATION_METADATA_SCHEMA_20260419_v0.md (new)
- formal/docs/release/SANDBOX_PROMOTION_PAYLOAD_REQUIREMENTS_20260419_v0.md (new)
- formal/docs/release/SANDBOX_PROMOTION_BOUNDED_PILOT_BINDING_COSMO_SR_CYCLE07_20260419_v0.json (new)
- formal/docs/release/SANDBOX_PHYSICS_LANE_EXECUTION_POLICY_20260418_v0.md (edit)
- formal/docs/release/PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0.md (edit)
- formal/python/tests/test_sandbox_promotion_phase2_phase4_contract_gate.py (new)
- formal/python/tests/test_sandbox_promotion_lane_policy_gate.py (edit)
- formal/python/tests/test_sandbox_promotion_migration_phase0_baseline_gate.py (edit)
- State_of_the_Theory.md (edit)
- formal/docs/paper/PHYSICS_ROADMAP_v0.md (edit)

## Out of scope
- governed promotion review wrapper declaration
- canonical mutation protocol implementation
- live writeback or row promotion execution
- pilot execution reruns or new physics claims
- full lane-boundary enforcement family expansion
- Phase 3, Phase 6, or Phase 7 closeout

## Acceptance
1. formal/python/tests/test_sandbox_promotion_phase2_phase4_contract_gate.py is green.
2. formal/python/tests/test_sandbox_promotion_lane_policy_gate.py remains green.
3. formal/python/tests/test_sandbox_promotion_migration_phase0_baseline_gate.py remains green.
4. State and roadmap mirrors pin the schema, payload contract, pilot binding, and revised next action.

## Rollback anchor
HEAD_AT_SANDBOX_PROMOTION_PHASE2_PHASE4_START

## Hard stop rule
If any file outside the Allowed files list changes before acceptance, stop immediately, restore the boundary, and treat the tranche as failed until scope is re-established.

## Boundary freshness note
This tranche defines metadata and payload discipline and binds one pilot track only. It does not yet authorize governed promotion review, canonical mutation, or pilot widening.