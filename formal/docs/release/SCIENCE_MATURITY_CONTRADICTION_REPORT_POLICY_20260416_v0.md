# Science Maturity Contradiction Report Policy (2026-04-16)

## Status
- ACTIVE
- Date: 2026-04-16
- Class: POLICY_NONCLAIM

## Objective
Define one fail-closed contradiction surface that makes maturity-surface claims and live blocker/seam truth disagreements explicit without changing any underlying authority source.

Qualified maturity rows are modeled, not contradictory, when the maturity registry explicitly declares that a bounded M4 artifact remains subject to a live theorem-gap qualifier.

## Required source bundle
- `formal/docs/release/PILLAR_DEEP_MATURITY_REGISTRY_v0.json`
- `formal/docs/release/PILLAR_DEEP_MATURITY_PROGRAM_v0.md`
- `formal/docs/release/TOE_GLOBAL_COMPLETION_MATRIX_v0.md`
- `formal/output/reports/seam_resolution_sla_ledger_20260416_v0.json`
- `formal/output/reports/blocker_burn_dashboard_20260416_v0.json`
- `formal/output/reports/physics_progress_ledger_v0.json`

## Required report fields
- `schema_id`
- `status`
- `captured_at_utc`
- `contradiction_status`
- `fail_conditions`
- `summary`
- `contradictions`
- `source_bundle`

## Exact fail conditions
- `PILLAR_M4_COMPLETE_VS_LIVE_THEOREM_GAP`
  Trigger: a pillar row is live in the completion matrix with blocker class `THEOREM_GAP` while the maturity registry marks the same pillar `m4_status: COMPLETE_BOUNDED_v0` and does not supply the explicit qualifier `m4_live_blocker_qualifier: LIVE_THEOREM_GAP_OPEN_v0`.
- `SEAM_PHYSICS_COMPLETE_VS_LIVE_HOLD_OR_PARITY`
  Trigger: a live seam ledger row has `physics_complete: true` while the same row still carries a held decision state or blocker class `PARITY_DRIFT` or `SEAM_INTEGRATION_GAP`.
- `LIVE_SEAM_ROW_MISSING_CANONICAL_STATUS`
  Trigger: a live seam row exists in the seam ledger but has no canonical seam-status coverage, producing `seam_status_resolution: MISSING_CANONICAL_SEAM_STATUS`.
- `STALE_READINESS_SIGNAL_WITH_PATHS_PINNED`
  Trigger: the blocker dashboard reports stale inputs while path-pinned readiness rows remain present under exception-required flat movement.

## Interpretation rules
- This report is additive and does not override the maturity registry, completion matrix, dashboard, or seam ledger.
- Presence of any contradiction forces `contradiction_status: FAIL_CLOSED_CONTRADICTIONS_PRESENT`.
- Qualified M4 rows with `m4_live_blocker_qualifier: LIVE_THEOREM_GAP_OPEN_v0` must be emitted as modeled observations so downstream tooling can still bind to the live blocker fact.
- The report exists to expose inconsistent reads, not to normalize or average them.

## Verification entry point
- Gate: `formal/python/tests/test_science_maturity_contradiction_report_live_gate.py`
- Tool test: `formal/python/tests/test_science_maturity_contradiction_report_generate.py`

## Non-claim boundary
This policy governs contradiction reporting only and does not authorize continuation, promotion, or external truth claims.