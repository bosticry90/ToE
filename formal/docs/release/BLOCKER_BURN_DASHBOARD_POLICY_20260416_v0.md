# Blocker Burn Dashboard Policy (2026-04-16)

## Status
- ACTIVE
- Date: 2026-04-16
- Class: POLICY_NONCLAIM

## Objective
Define one canonical blocker-burn dashboard payload derived directly from the completion matrix and existing blocker/report artifacts so tranche reviews can measure blocker reduction without creating a second authority source.

## Required dashboard fields
- `schema_id`
- `status`
- `captured_at_utc`
- `window`
- `tranche_id`
- `blocker_scoreboard`
- `row_blocker_contributions`
- `row_promotion_readiness`
- `closure_map_linkage`
- `tranche_timeline`
- `source_freshness`
- `source_bundle`

## Required source bundle
- `formal/docs/release/TOE_GLOBAL_COMPLETION_MATRIX_v0.md`
- `formal/output/reports/governance_blocker_trend_window_20260410_v0.json`
- `formal/output/reports/governance_blocker_closure_map_20260410_v0.json`
- `formal/output/reports/physics_progress_ledger_v0.json`
- `formal/output/reports/convergence_baseline_pack_20260409_v0.json`

## Dashboard rules
- Blocker counts and rolling-window semantics remain matrix-authoritative.
- Dashboard deltas must reconcile with the blocker trend window report.
- Row blocker contribution must derive from current completion-matrix row assignments.
- Row promotion readiness may report pinned-path readiness only; it must not claim gate passing unless gate evidence is explicitly sourced.
- Source freshness warnings are mandatory when any required input lags the newest captured source.
- If net blocker delta is non-negative across the active review window, the dashboard must surface the exception-artifact requirement.

## Verification entry point
- Gate: `formal/python/tests/test_blocker_burn_dashboard_live_gate.py`
- Tool test: `formal/python/tests/test_blocker_burn_dashboard_generate.py`

## Non-claim boundary
This dashboard governs repository-local blocker tracking and does not assert scientific adequacy or promotion sufficiency by itself.