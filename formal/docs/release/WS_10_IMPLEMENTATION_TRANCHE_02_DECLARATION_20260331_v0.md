# WS-10 Implementation Tranche 02 Declaration (2026-03-31)

## Tranche name
WS_10_IMPLEMENTATION_TRANCHE_02_FULL_PYTEST_BLOCKER_REPAIR

## Objective
Repair exactly the current five full-pytest blockers (schema/governance alignment) without introducing policy weakening or scope expansion.

## Allowed files
- formal/python/tests/test_architecture_schema_enforcement.py (compatibility clarification only, no policy weakening)
- formal/python/tests/test_new_pillar_must_pass_template.py (compatibility clarification only, no policy weakening)
- formal/python/tests/test_governance_surface_growth_guard.py (if lock artifact path requires update only)
- formal/python/tests/test_fn01_candidate_table.py (only if parser path needs compatibility clarification)
- formal/docs/paper/DERIVATION_TARGET_*.md files explicitly named in failing test output
- Governance growth lock/policy artifact directly referenced by test_governance_surface_growth_guard.py
- BOM-affected file(s) reported by failing pytest output under formal/python/tests

## Out of scope
- New lanes, new cycle content, empirical comparator recovery, broad template normalization outside failing files, unrelated governance refactors.

## Acceptance
1) Targeted rerun of the five failing tests is green.
2) Full formal/python/tests suite is green.
3) ./checkpoint_ladder.ps1 is green end-to-end.
4) Generated outputs restored as needed and working tree clean.

## Rollback anchor
5d6bb56

## Hard stop rule
If any file outside Allowed files changes, stop immediately and treat tranche as failed until drift is reverted.