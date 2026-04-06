# WS-10 Implementation Tranche 25 Declaration (2026-04-05)

## Tranche name
WS_10_IMPLEMENTATION_TRANCHE_25_PHASE_E_DUAL_CANDIDATE_PREDECISION

## Objective
Execute a declaration-first, authorization-only tranche that pins exactly two matched A1 candidate artifacts for later selection while explicitly forbidding execution-live semantics before a separate decision tranche.

## Allowed files
- formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_25_DECLARATION_20260405_v0.md (new)
- formal/docs/release/WS_10_T25_A1_GR_QM_SEAM_PROMOTION_MICRO_CANDIDATE_v0.md (new)
- formal/docs/release/WS_10_T25_A1_BR01_DISPERSION_TO_METRIC_MICRO_CANDIDATE_v0.md (new)
- formal/output/ws10_t25_dual_candidate_preauthorization_checkpoint_20260405_v0.json (new)
- formal/python/tests/test_ws10_t25_dual_candidate_authorization_gate.py (new)
- State_of_the_Theory.md (edit)
- formal/docs/paper/PHYSICS_ROADMAP_v0.md (edit)
- formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md (edit)

## Out of scope
- theorem-body edits in Lean surfaces
- lane execution authorization
- lane execution-live tokens
- release-gate truth policy changes
- Packet42 policy changes
- scalar freeze policy changes
- class flips or physics-complete status flips

## Acceptance
1. formal/python/tests/test_ws10_t25_dual_candidate_authorization_gate.py is green.
2. Full formal/python/tests suite is green.
3. pwsh -NoProfile -ExecutionPolicy Bypass -File ./checkpoint_ladder.ps1 is green end-to-end.
4. Working tree is clean after generated-output restore.

## Rollback anchor
28f228f

## Hard stop rule
If any file outside the Allowed files list changes before acceptance, stop immediately, revert drift, and treat this tranche as failed until boundaries are restored.

## Boundary freshness note
This tranche is candidate pre-decision only. Lane authorization must occur in a separate tranche, and execution begins only after that decision tranche is accepted.
