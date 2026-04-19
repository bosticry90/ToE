# Sandbox Promotion Migration Phase 0 Declaration (2026-04-19)

## Tranche name
SANDBOX_PROMOTION_MIGRATION_PHASE0_BASELINE_KICKOFF

## Objective
Open the bounded Phase 0 tranche for the sandbox-first promotion-gated governance migration by pinning the baseline dossier, phase ledger, and next-action contract before artifact classification or promotion payload expansion.

## Allowed files
- formal/docs/release/SANDBOX_PROMOTION_MIGRATION_PHASE0_DECLARATION_20260419_v0.md (new)
- formal/output/reports/sandbox_promotion_migration_phase0_baseline_dossier_20260419_v0.json (new)
- formal/python/tests/test_sandbox_promotion_migration_phase0_baseline_gate.py (new)
- formal/python/tests/test_sandbox_promotion_lane_policy_gate.py (edit)
- State_of_the_Theory.md (edit)
- formal/docs/paper/PHYSICS_ROADMAP_v0.md (edit)

## Out of scope
- edits to sandbox-lane policy semantics
- edits to promotion-lane policy semantics
- artifact classification rule details
- promotion payload schema details
- governed promotion review wrapper declaration
- canonical row or seam mutation protocol changes
- pilot-track execution changes

## Acceptance
1. formal/python/tests/test_sandbox_promotion_migration_phase0_baseline_gate.py is green.
2. formal/python/tests/test_sandbox_promotion_lane_policy_gate.py remains green.
3. State and roadmap mirrors pin the Phase 0 baseline dossier and revised next action.

## Rollback anchor
HEAD_AT_SANDBOX_PROMOTION_PHASE0_START

## Hard stop rule
If any file outside the Allowed files list changes before acceptance, stop immediately, restore the boundary, and treat the tranche as failed until scope is re-established.

## Boundary freshness note
This tranche is Phase 0 framing only. It formalizes the migration baseline and phase accounting without yet introducing artifact classification contracts, promotion payload requirements, or live promotion execution.