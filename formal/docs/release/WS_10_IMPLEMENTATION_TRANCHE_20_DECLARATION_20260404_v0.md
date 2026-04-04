# WS-10 Implementation Tranche 20 Declaration (2026-04-04)

## Tranche name
WS_10_IMPLEMENTATION_TRANCHE_20_REMEDIATION_PROGRAM_PHASE_A_KICKOFF

## Objective
Start the comprehensive remediation program with one bounded kickoff packet that pins scope, baseline snapshot metadata, and minimal authority-surface visibility for architecture/automation/governance hardening without changing physics claim posture.

## Allowed files
- formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_20_DECLARATION_20260404_v0.md (new)
- formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md (new)
- formal/output/ws10_remediation_baseline_snapshot_20260404_v0.json (new)
- formal/python/tests/test_ws10_t20_remediation_kickoff_gate.py (new)
- State_of_the_Theory.md (edit)
- formal/docs/paper/PHYSICS_ROADMAP_v0.md (edit)
- GOVERNANCE_VERSION_v2.lock (edit, governance baseline count sync only)

## Out of scope
- all derivation target theorem surfaces
- seam status class flips or physics-complete status changes
- Packet41 and Packet42 policy changes
- scalar freeze policy changes
- release-gate truth command changes
- broad architecture refactors in this tranche

## Acceptance
1. formal/python/tests/test_ws10_t20_remediation_kickoff_gate.py is green.
2. Full formal/python/tests suite is green.
3. ./checkpoint_ladder.ps1 is green end-to-end.
4. Generated outputs are restored as needed and the working tree is clean afterward.

## Rollback anchor
95def34

## Hard stop rule
If any file outside the Allowed files list changes before acceptance, stop immediately, revert the drift, and treat the tranche as failed until the boundary is restored.

## Boundary freshness note
This tranche is kickoff-only and intentionally limited to execution framing, baseline metadata pinning, and authority visibility tokens for the remediation program.