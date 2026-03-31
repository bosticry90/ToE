# WS-10 Implementation Tranche 04 Declaration (2026-03-31)

## Tranche name
WS_10_IMPLEMENTATION_TRANCHE_04_GOVERNANCE_GROWTH_GUARD_ACCOMMODATION

## Objective
Allow the next bounded science doc delta by resolving the currently observed governance growth-guard breach (`governance_docs: observed=390, allowed=388`) using the minimum policy/lock accommodation required by the existing repo contract.

## Allowed files
- `GOVERNANCE_VERSION_v2.lock`
- `formal/python/tests/test_governance_surface_growth_guard.py` (only if compatibility clarification is strictly required; do not weaken policy)
- any single explicit authority/reference surface only if the lock contract or the growth-guard test directly requires it

## Out of scope
- any science doc or synthesis doc
- any new lane or cycle content
- any schema refactor unrelated to growth accommodation
- any empirical comparator recovery
- any broad governance cleanup or unrelated policy changes
- any edits to `State_of_the_Theory.md` or `formal/docs/paper/PHYSICS_ROADMAP_v0.md` unless directly required by the growth-lock contract

## Acceptance
1. `formal/python/tests/test_governance_surface_growth_guard.py` is green.
2. Full `formal/python/tests` suite is green.
3. `./checkpoint_ladder.ps1` is green end-to-end.
4. Generated outputs are restored as needed and the working tree is clean afterward.

## Rollback anchor
369c91b

## Hard stop rule
If any file outside the Allowed files list changes during this tranche, stop immediately, revert the drift, and treat the tranche as failed until the boundary is restored.
