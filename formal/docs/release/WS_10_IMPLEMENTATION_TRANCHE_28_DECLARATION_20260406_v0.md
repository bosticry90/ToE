# WS-10 Implementation Tranche 28 Declaration (2026-04-06)

## Tranche name
WS_10_IMPLEMENTATION_TRANCHE_28_PHASE_B_BOUNDED_GR_QM_EXECUTION_CHECKPOINT

## Objective
Execute the first bounded post-T27 GR-QM execution checkpoint tranche under single-lane non-live scope, pinning checkpoint semantics and verification ladder without introducing execution-live tokens.

## Allowed files
- formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_28_DECLARATION_20260406_v0.md (new)
- formal/docs/release/WS_10_T28_GR_QM_BOUNDED_EXECUTION_CHECKPOINT_20260406_v0.md (new)
- formal/output/ws10_t28_gr_qm_bounded_execution_checkpoint_20260406_v0.json (new)
- formal/python/tests/test_ws10_t28_gr_qm_bounded_execution_checkpoint_gate.py (new)
- State_of_the_Theory.md (edit)
- formal/docs/paper/PHYSICS_ROADMAP_v0.md (edit)
- formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md (edit)

## Out of scope
- release-gate truth policy changes
- Packet42 policy changes
- scalar freeze policy changes
- BR01 lane reactivation
- execution-live lane activation
- claim-level promotion language changes

## Bounded execution requirements
- tranche remains single-lane and non-live.
- execution checkpoint is tied to formal/toe_formal/ToeFormal/Bridges/GR_QM_SeamPromotion.lean.
- checkpoint explicitly pins cycle01/02/03 gate ladder compatibility.
- execution-live token count remains zero across parity surfaces.

## Acceptance
1. formal/python/tests/test_ws10_t28_gr_qm_bounded_execution_checkpoint_gate.py is green.
2. Focused boundary ladder is green.
3. Full formal/python/tests suite is green.
4. Working tree is clean after generated-output restore.

## Rollback anchor
522eedb

## Hard stop rule
If scope drifts outside the Allowed files list before acceptance, stop and treat the tranche as failed until boundaries are restored.

## Boundary freshness note
This tranche is execution-checkpoint only and remains non-live under the T27 lock contract.
