# WS-10 Implementation Tranche 26 Declaration (2026-04-06)

## Tranche name
WS_10_IMPLEMENTATION_TRANCHE_26_PHASE_E_SINGLE_LANE_DECISION

## Objective
Execute a declaration-first, decision-only tranche that selects exactly one authorized lane from the two T25 pinned A1 candidates while keeping the non-selected lane paused/deferred and preserving non-live semantics.

## Allowed files
- formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_26_DECLARATION_20260406_v0.md (new)
- formal/docs/release/WS_10_T26_DUAL_CANDIDATE_LANE_SELECTION_DECISION_20260406_v0.md (new)
- formal/output/ws10_t26_single_lane_authorization_checkpoint_20260406_v0.json (new)
- formal/python/tests/test_ws10_t26_dual_candidate_lane_selection_gate.py (new)
- State_of_the_Theory.md (edit)
- formal/docs/paper/PHYSICS_ROADMAP_v0.md (edit)
- formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md (edit)

## Out of scope
- theorem-body edits in Lean surfaces
- direct lane execution authorization
- any execution-live tokens
- release-gate truth policy changes
- Packet42 policy changes
- scalar freeze policy changes
- class flips or physics-complete status flips

## Decision style
- OPTION_A_DIRECT_WINNER_WITH_BRIEF_RUBRIC_SUMMARY
- winner is declared directly in one decision artifact
- rubric summary is required but remains brief and non-scored

## Acceptance
1. formal/python/tests/test_ws10_t26_dual_candidate_lane_selection_gate.py is green.
2. Full formal/python/tests suite is green.
3. pwsh -NoProfile -ExecutionPolicy Bypass -File ./checkpoint_ladder.ps1 is green end-to-end.
4. Working tree is clean after generated-output restore.

## Rollback anchor
522eedb

## Hard stop rule
If any file outside the Allowed files list changes before acceptance, stop immediately, revert drift, and treat this tranche as failed until boundaries are restored.

## Boundary freshness note
This tranche is decision-only and non-live. A future tranche is required for execution semantics after this decision is accepted.
