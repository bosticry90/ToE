# WS-10 Implementation Tranche 12 Declaration (2026-04-01)

## Tranche name
WS_10_IMPLEMENTATION_TRANCHE_12_GROWTH_GUARD_ACCOMMODATION_GOVDOC_394

## Objective
Accommodate only the newly observed governance growth-guard breach (`governance_docs: observed=394, allowed=392`) with the minimum bounded lock/test compatibility change required by repo policy.

## Allowed files
- `GOVERNANCE_VERSION_v2.lock`
- `formal/python/tests/test_governance_surface_growth_guard.py` only if strictly necessary for compatibility clarification (no policy weakening)

## Out of scope
- all science docs
- all synthesis docs
- all new tranche-local gates
- all schema edits
- broad governance cleanup or unrelated governance refactors
- any authority/parity surface changes unrelated to this specific growth accommodation

## Acceptance
1. `formal/python/tests/test_governance_surface_growth_guard.py` is green.
2. Full `formal/python/tests` suite is green.
3. `./checkpoint_ladder.ps1` is green end-to-end.
4. Generated outputs are restored as needed and the working tree is clean afterward.

## Rollback anchor
acda7fa

## Hard stop rule
If any file outside the Allowed files list changes before acceptance, stop immediately, revert the drift, and treat the tranche as failed until the boundary is restored.

## Reopen gate
Do not reopen the Increment68 science tranche until this accommodation tranche is accepted.
