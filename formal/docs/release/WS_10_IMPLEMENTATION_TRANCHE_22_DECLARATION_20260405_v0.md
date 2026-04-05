# WS-10 Implementation Tranche 22 Declaration (2026-04-05)

## Tranche name
WS_10_IMPLEMENTATION_TRANCHE_22_REMEDIATION_PHASE_C_LEAN_PROOF_DEBT_LEDGER_KICKOFF

## Objective
Start bounded Phase C remediation by pinning a Lean proof-debt operational checkpoint that fixes A1/A2/A3 and variational-package sequencing as executable governance metadata, without changing theorem claims or release-gate truth policy.

## Allowed files
- formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_22_DECLARATION_20260405_v0.md (new)
- formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md (edit)
- formal/output/ws10_lean_proof_debt_ledger_checkpoint_20260405_v0.json (new)
- formal/python/tests/test_ws10_t22_lean_proof_debt_ledger_gate.py (new)
- State_of_the_Theory.md (edit)
- formal/docs/paper/PHYSICS_ROADMAP_v0.md (edit)

## Out of scope
- derivation theorem-body edits
- seam class flips or physics-complete status flips
- Packet41/Packet42 policy changes
- scalar freeze policy changes
- release-gate truth policy changes
- variational theorem discharge claims

## Acceptance
1. formal/python/tests/test_ws10_t22_lean_proof_debt_ledger_gate.py is green.
2. Full formal/python/tests suite is green.
3. ./checkpoint_ladder.ps1 is green end-to-end.
4. Generated outputs are restored as needed and the working tree is clean afterward.

## Rollback anchor
269cd81

## Hard stop rule
If any file outside the Allowed files list changes before acceptance, stop immediately, revert the drift, and treat the tranche as failed until the boundary is restored.

## Boundary freshness note
This tranche is ledger-kickoff only and intentionally constrained to checkpoint metadata, parity token wiring, and gate enforcement for Phase C start.
