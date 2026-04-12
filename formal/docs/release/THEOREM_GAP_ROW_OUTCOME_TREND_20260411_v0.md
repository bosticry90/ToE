# THEOREM_GAP_ROW_OUTCOME_TREND_20260411_v0

## Status
- ACTIVE_NONLIVE_NONCLAIM
- Date: 2026-04-11

## Objective
Provide row-level stagnation visibility by aggregating theorem-gap tranche outcomes as success/failure/no_change counts per row over time.

## Required controls
1. Outcome aggregation must be materialized per theorem-gap row.
2. Registry entries must map to canonical theorem-gap rows.
3. Stagnation rows must be explicitly surfaced when rows have no success outcomes.
4. Objective completion requires at least one row success and zero stagnation rows.

## Required report pointer
- formal/output/reports/theorem_gap_row_outcome_trend_20260411_v0.json

## Governance gate pointer
- formal/python/tests/test_governance_audit_packet_gate.py

## Non-claim boundary
Repository-local theorem-gap row outcome trend policy only; no scientific adequacy claim.