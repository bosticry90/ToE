# WS-10 Implementation Tranche 17 Declaration (2026-04-01)

## Tranche name
WS_10_IMPLEMENTATION_TRANCHE_17_GROWTH_POLICY_SOURCE_UNIFICATION

## Objective
Unify growth-policy control-plane truth by making governance document inventory inputs explicit and schema-declared, wiring the growth guard to consume that declaration, and synchronizing the tracked schema hash in the active governance lock without widening into manifest refactors.

## Allowed files
- formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_17_DECLARATION_20260401_v0.md (new)
- ARCHITECTURE_SCHEMA_v1.json (edit)
- formal/python/tests/test_governance_surface_growth_guard.py (edit)
- formal/python/tests/test_governance_surface_inventory_contract.py (new)
- GOVERNANCE_VERSION_v2.lock (edit)

## Out of scope
- governance_suite.ps1 manifest reduction work (reserved for next tranche)
- checkpoint_ladder.ps1 behavior changes
- State_of_the_Theory.md and physics/science lane payload edits
- derivation target content changes
- lock version bump and new lock file families
- tooling regeneration architecture changes

## Acceptance
1. Growth-policy guard and new inventory contract test are green.
2. Full formal/python/tests suite is green.
3. ./checkpoint_ladder.ps1 is green end-to-end.
4. Generated outputs are restored as needed and the working tree is clean afterward.

## Rollback anchor
6cde61b

## Hard stop rule
If any file outside the Allowed files list changes before acceptance, stop immediately, revert the drift, and treat the tranche as failed until the boundary is restored.

## Boundary freshness note
This declaration opens the first control-plane reduction tranche after Tranche 16 acceptance and is intentionally scoped to Recommendation 1 only.
