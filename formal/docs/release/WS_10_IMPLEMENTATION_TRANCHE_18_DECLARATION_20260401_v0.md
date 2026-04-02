# WS-10 Implementation Tranche 18 Declaration (2026-04-01)

## Tranche name
WS_10_IMPLEMENTATION_TRANCHE_18_GOVERNANCE_SUITE_MANIFEST_REDUCTION

## Objective
Replace a bounded portion of the hand-maintained governance suite pytest list with a deterministic manifest-driven selection mechanism while preserving identical effective lane coverage through explicit equivalence gating.

## Allowed files
- formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_18_DECLARATION_20260401_v0.md (new)
- governance_suite.ps1 (edit)
- formal/docs/release/GOVERNANCE_TEST_MANIFEST_v1.json (new)
- formal/python/tools/governance_manifest_select.py (new)
- formal/python/tests/test_governance_suite_manifest_equivalence_gate.py (new)

## Out of scope
- growth-policy schema/lock semantics and inventory counting logic
- checkpoint_ladder.ps1 behavior changes
- State_of_the_Theory.md and all physics/science payload surfaces
- broad governance suite redesign beyond bounded manifest substitution
- lock version bumps and architecture schema version changes
- orchestration manifest expansion beyond what is required for equivalence verification

## Acceptance
1. Targeted manifest-equivalence gate is green and demonstrates no unintended test-lane coverage loss.
2. Full formal/python/tests suite is green.
3. ./checkpoint_ladder.ps1 is green end-to-end.
4. Generated outputs are restored as needed and the working tree is clean afterward.

## Rollback anchor
a42300b

## Hard stop rule
If any file outside the Allowed files list changes before acceptance, stop immediately, revert the drift, and treat the tranche as failed until the boundary is restored.

## Boundary freshness note
This declaration opens Recommendation 2 implementation immediately after accepted Tranche 17 and is intentionally scoped to governance-suite manifest reduction with strict equivalence discipline.
