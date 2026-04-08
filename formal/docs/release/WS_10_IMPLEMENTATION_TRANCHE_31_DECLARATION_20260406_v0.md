# WS-10 Implementation Tranche 31 Declaration (2026-04-06)

## Tranche name
WS_10_IMPLEMENTATION_TRANCHE_31_PHASE_E_PROOF_DEBT_COUPLING

## Objective
Start Phase E by coupling proof-debt traceability and burndown checkpoint surfaces so debt-to-witness mappings are explicit, parity-pinned, and non-orphaned under non-live governance posture.

## Allowed files
- formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_31_DECLARATION_20260406_v0.md (new)
- formal/docs/release/WS_10_T31_PROOF_DEBT_COUPLING_DECISION_20260406_v0.md (new)
- formal/output/ws10_t31_proof_debt_coupling_checkpoint_20260406_v0.json (new)
- formal/python/tests/test_ws10_t31_proof_debt_coupling_gate.py (new)
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

## Phase-E requirements
- Proof-debt traceability surface remains explicit and stable.
- Burndown cycle05 packet/checkpoint pointers remain explicit and stable.
- No orphan proof-debt marker bindings are permitted.
- active lane remains A1_GR_QM_SEAM_PROMOTION.
- paused lane remains A1_BR01_DISPERSION_TO_METRIC.
- execution-live token count remains zero.

## Acceptance
1. formal/python/tests/test_ws10_t31_proof_debt_coupling_gate.py is green.
2. Proof-debt focused gate bundle is green.
3. Full formal/python/tests suite is green.
4. Working tree is clean after generated-output restore.

## Rollback anchor
522eedb

## Hard stop rule
If any scope drift occurs beyond the Allowed files list, stop and treat this tranche as failed until boundaries are restored.

## Boundary freshness note
This tranche is control-surface proof-debt coupling only and does not authorize live execution semantics.
