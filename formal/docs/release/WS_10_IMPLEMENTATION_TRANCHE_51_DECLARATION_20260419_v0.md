# WS-10 Implementation Tranche 51 Declaration (2026-04-19)

## Tranche name
WS_10_IMPLEMENTATION_TRANCHE_51_POST_PLAN_AUTHORITY_SOURCE_CUTOVER

## Objective
Execute the bounded strict-authority tranche after T50 by pinning the post-plan Phase 3 through Phase 6 stack as the single active repo-governance source-of-truth for current reads, while demoting restart-era surfaces to traceability-only status under the existing consolidation memo rather than allowing mixed authority residency.

## Allowed files
- formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_51_DECLARATION_20260419_v0.md (new)
- formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md (edit)
- formal/output/reports/ws10_t51_post_plan_authority_source_cutover_20260419_v0.json (new, generated)
- formal/python/tools/ws10_t51_post_plan_authority_source_cutover_report.py (new)
- formal/python/tests/test_ws10_t51_post_plan_authority_source_cutover_gate.py (new)
- State_of_the_Theory.md (edit)
- formal/docs/paper/PHYSICS_ROADMAP_v0.md (edit)

## Out of scope
- reopening restart-era execution lanes
- altering scientific truth, theorem status, or seam status
- changing the post-plan canonical reports themselves
- introducing a new live execution row
- broad suite reruns or performance-policy changes

## Acceptance
1. formal/python/tests/test_ws10_t51_post_plan_authority_source_cutover_gate.py is green.
2. The generated cutover report matches the current consolidation memo plus T50 alignment state.
3. Focused state and roadmap parity bundle is green.
4. The next action points to whole-program acceptance review rather than another authority fork.

## Rollback anchor
HEAD_AT_T51_START

## Hard stop rule
If any file outside the Allowed files list changes before acceptance, stop immediately, restore the boundary, and treat the tranche as failed until scope is re-established.

## Boundary freshness note
This tranche pins strict authority residency only. It does not claim blocker movement, scientific adequacy, or Phase 6 acceptance closeout by itself.