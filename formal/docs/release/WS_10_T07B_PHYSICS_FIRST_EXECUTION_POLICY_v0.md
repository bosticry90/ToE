# WS_10_T07B_PHYSICS_FIRST_EXECUTION_POLICY_v0

## Status
- ACTIVE
- Date: 2026-03-26
- Workstream: WS-10
- Task ID: WS-10-T07B

## Objective
Enforce a physics-first execution posture for the active restart lane so scientific closure blockers are prioritized ahead of governance expansion work, while keeping release-gate truth and non-claim controls unchanged.

## Scope
In scope:
- publish explicit physics-first policy rules for active restart execution.
- mirror policy tokens across tracker, state, and roadmap authority surfaces.
- preserve scalar freeze and Packet42 hold invariance.

Out of scope:
- theorem-surface edits.
- packet hold release.
- scalar freeze release.
- release-gate contract changes.

## Policy Rules
- Priority rule: `PHYSICS_BLOCKER_FIRST_GOVERNANCE_UNBLOCKER_ONLY`.
- Governance role in this phase: enabling lane for parity, safety, and claim-boundary integrity.
- Release-gate truth remains unchanged:
  - governance prerequisite lane: `pwsh -NoProfile -ExecutionPolicy Bypass -File ./governance_suite.ps1`
  - branch-health lane: `./py.ps1 -m pytest formal/python/tests -q`
- Non-claim boundary remains unchanged.

## Enforcement Semantics
- If a governance change does not directly unblock the active physics lane or preserve non-claim integrity, defer it.
- Keep one active physics lane and avoid parallel theorem-lane expansion.
- Treat cross-surface token parity as mandatory for policy enforcement claims.

## Validation Ladder
1. `./py.ps1 -m pytest -q formal/python/tests/test_state_theory_dag.py formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py`
2. `./py.ps1 -m pytest -q formal/python/tests/test_toe_seam_status_split_gate.py`

## Evidence
- 2026-03-26: policy tokens mirrored in `State_of_the_Theory.md` and `formal/docs/paper/PHYSICS_ROADMAP_v0.md`.
- 2026-03-26: tracker and WS-10 task tables updated to include WS-10-T07B checkpoint semantics.
- 2026-03-26: README policy checkpoint added with unchanged release-gate contract wording.

## Exit Criteria
- Physics-first policy tokens are present and consistent across tracker, state, and roadmap surfaces.
- Release-gate truth text remains unchanged in meaning.
- Validation ladder is green with no theorem-surface edits in the checkpoint tranche.
