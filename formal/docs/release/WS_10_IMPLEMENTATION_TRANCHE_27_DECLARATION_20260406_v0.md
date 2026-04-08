# WS-10 Implementation Tranche 27 Declaration (2026-04-06)

## Tranche name
WS_10_IMPLEMENTATION_TRANCHE_27_PHASE_E_SINGLE_LANE_SCOPE_LOCK

## Objective
Lock the post-T26 single-lane boundary into one explicit non-live scope artifact that pins target lane, allowed file residency, verification ladder, and stop condition before any theorem-surface execution tranche.

## Allowed files
- formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_27_DECLARATION_20260406_v0.md (new)
- formal/docs/release/WS_10_T27_SINGLE_LANE_SCOPE_LOCK_20260406_v0.md (new)
- formal/output/ws10_t27_scope_lock_checkpoint_20260406_v0.json (new)
- formal/python/tests/test_ws10_t27_single_lane_scope_lock_gate.py (new)
- State_of_the_Theory.md (edit)
- formal/docs/paper/PHYSICS_ROADMAP_v0.md (edit)
- formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md (edit)

## Out of scope
- theorem-body edits in Lean surfaces
- execution-live lane activation
- release-gate truth policy changes
- Packet42 policy changes
- scalar freeze policy changes
- claim or publication promotion language changes

## Scope-lock requirements
- exactly one scope-lock artifact is required for T27.
- authorized lane remains A1_GR_QM_SEAM_PROMOTION and paused lane remains A1_BR01_DISPERSION_TO_METRIC.
- execution-live token count remains zero.
- stop condition token must be present and enforced.

## Acceptance
1. formal/python/tests/test_ws10_t27_single_lane_scope_lock_gate.py is green.
2. Full formal/python/tests suite is green.
3. pwsh -NoProfile -ExecutionPolicy Bypass -File ./checkpoint_ladder.ps1 is green end-to-end.
4. Working tree is clean after generated-output restore.

## Rollback anchor
522eedb

## Hard stop rule
If any file outside the Allowed files list changes before acceptance, stop immediately, revert drift, and treat this tranche as failed until boundaries are restored.

## Boundary freshness note
This tranche remains non-live and control-surface only. It does not authorize theorem-surface execution by itself.
