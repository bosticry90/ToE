# WS-10 Implementation Tranche 32 Declaration (2026-04-06)

## Tranche name
WS_10_IMPLEMENTATION_TRANCHE_32_PHASE_F_AUTHORITY_CONVERGENCE

## Objective
Execute Phase F closeout by converging authority-surface status tokens and final acceptance anchors after T31 while preserving non-live single-lane non-claim posture.

## Allowed files
- formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_32_DECLARATION_20260406_v0.md (new)
- formal/docs/release/WS_10_T32_AUTHORITY_CONVERGENCE_DECISION_20260406_v0.md (new)
- formal/output/ws10_t32_authority_convergence_checkpoint_20260406_v0.json (new)
- formal/python/tests/test_ws10_t32_authority_convergence_gate.py (new)
- State_of_the_Theory.md (edit)
- formal/docs/paper/PHYSICS_ROADMAP_v0.md (edit)
- formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md (edit)

## Out of scope
- execution-live lane activation
- dual-lane reopening
- BR01 reactivation
- Packet42 policy changes
- scalar freeze policy changes
- theorem-body edits
- release-gate truth policy changes

## Phase-F requirements
- authority-surface convergence status is explicit and parity-pinned.
- final acceptance ladder pointers are explicit.
- active lane remains A1_GR_QM_SEAM_PROMOTION.
- paused lane remains A1_BR01_DISPERSION_TO_METRIC.
- execution-live token count remains zero.

## Acceptance
1. formal/python/tests/test_ws10_t32_authority_convergence_gate.py is green.
2. Phase-F parity bundle is green.
3. Full formal/python/tests suite is green.
4. Working tree is clean after generated-output restore.

## Rollback anchor
522eedb

## Hard stop rule
If any scope drift occurs beyond the Allowed files list, stop and treat this tranche as failed until boundaries are restored.

## Boundary freshness note
This tranche is authority-convergence control-surface work only and does not authorize live execution semantics.
