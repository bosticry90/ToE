# WS-10 Implementation Tranche 24 Declaration (2026-04-05)

## Tranche name
WS_10_IMPLEMENTATION_TRANCHE_24_REMEDIATION_PHASE_E_PREAUTHORIZATION

## Objective
Execute a bounded governance tranche that pre-authorizes Phase E by pinning entry criteria, declaration pointers, and enforcement gates without changing theorem bodies or seam-physics claim posture.

## Allowed files
- formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_24_DECLARATION_20260405_v0.md (new)
- formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md (edit)
- formal/output/ws10_t24_phase_e_preauthorization_checkpoint_20260405_v0.json (new)
- formal/python/tests/test_ws10_t24_phase_e_preauthorization_gate.py (new)
- State_of_the_Theory.md (edit)
- formal/docs/paper/PHYSICS_ROADMAP_v0.md (edit)

## Out of scope
- theorem-body edits in Lean surfaces
- class flips or physics-complete status flips
- Packet41/Packet42 policy changes
- scalar freeze policy changes
- release-gate truth policy changes
- restoring or applying isolated stash artifacts into live tree

## Acceptance
1. formal/python/tests/test_ws10_t24_phase_e_preauthorization_gate.py is green.
2. Full formal/python/tests suite is green.
3. pwsh -NoProfile -ExecutionPolicy Bypass -File ./checkpoint_ladder.ps1 is green end-to-end.
4. Working tree is clean after generated-output restore.

## Rollback anchor
ec19bf7

## Hard stop rule
If any file outside the Allowed files list changes before acceptance, stop immediately, revert drift, and treat this tranche as failed until boundaries are restored.

## Boundary freshness note
This tranche is pre-authorization only. Science implementation begins in a separate A1 tranche after full acceptance.
