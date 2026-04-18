# WS-10 TGC-94 EM Micro-27 Authorization Decision Package (2026-04-18)

## Status
- ACTIVE
- Date: 2026-04-18
- Tranche: TGC-94
- Class: AUTHORIZATION_CONTROL_PARITY_PACKAGE_NONCLAIM

## Objective
Mirror the already-materialized EM Micro-27 authorization-control result into a release-style governance review surface so the repo does not rely on inference from state and report artifacts alone.

## Inputs audited
- `formal/output/reports/em_u1_micro26_double_divergence_binding_theorem_closeout_decision_20260417_v0.json`
- `formal/output/reports/em_u1_micro27_authorization_decision_20260418_v0.json`
- `formal/output/reports/science_maturity_contradiction_report_20260416_v0.json`
- `State_of_the_Theory.md`
- `formal/docs/paper/PHYSICS_ROADMAP_v0.md`

## Canonical decision tokens
- `TGC94_EM_MICRO26_BOUNDARY_CONTINUITY_v0: RETAIN_MICRO26_BOUNDED_ENDPOINT_v0`
- `TGC94_EM_MICRO27_DECISION_v0: KEEP_MICRO27_CLOSED_v0`
- `TGC94_EM_MICRO27_AUTHORIZATION_STATUS_v0: NOT_AUTHORIZED_PENDING_DISTINCT_MICRO27_DECISION_v0`
- `TGC94_EM_MICRO27_PROGRESS_AUTOMATION_v0: GLOBAL_PROGRESS_DOES_NOT_AUTHORIZE_EM_FOLLOW_ON`
- `TGC94_EM_MICRO27_REQUIRED_AUTHORIZATION_BASIS_v0: EM_LOCAL_BLOCKER_EVENT_OR_EXPLICIT_MICRO27_AUTHORIZATION_TRANCHE`
- `TGC94_EM_LIVE_ROW_CONTRADICTION_v0: ROW_PILLAR_EM_001_REMAINS_LIVE_THEOREM_GAP`

## Decision rule
- If the Micro-26 closeout surface still requires explicit Micro-27 authorization and `ROW-PILLAR-EM-001` remains a live theorem-gap contradiction, then:
  - `TGC94_EM_MICRO27_DECISION_v0` must be `KEEP_MICRO27_CLOSED_v0`.
  - `TGC94_EM_MICRO27_AUTHORIZATION_STATUS_v0` must be `NOT_AUTHORIZED_PENDING_DISTINCT_MICRO27_DECISION_v0`.
- `PROGRESS` in the global physics ledger is insufficient on its own to authorize EM follow-on.
- Any future Micro-27 activation requires a changed EM-local authorization basis rather than a momentum readout from global blocker movement.

## Governance interpretation
- Micro-26 remains the retained bounded endpoint.
- The Micro-27 authorization-control surface is real and explicit, not implied.
- The present release outcome is a hold decision, not an implementation opening.
- The next clean tranche is either:
  - a changed EM-local blocker basis, or
  - a separate already-authorized lane.

## Required parity surfaces
- `State_of_the_Theory.md`
- `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
- `formal/docs/release/WS_10_THEORY_RESTART_PILOT_PLAN_v0.md`

## Validation Bundle
1. `./py.ps1 -m pytest -q formal/python/tests/test_em_u1_micro27_authorization_decision_report.py`
2. `./py.ps1 -m pytest -q formal/python/tests/test_ws10_tgc94_em_micro27_authorization_decision_package.py`

## Non-claim boundary
This package records repository-local EM authorization-control parity only. It does not authorize Micro-27 execution, does not claim theorem discharge, and does not assert external-truth adequacy.