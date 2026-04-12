# THEOREM_GAP_QM_REWORK_TRANCHE_20260411_v0

## Status
- ACTIVE_NONLIVE_NONCLAIM
- Date: 2026-04-11

## Objective
Execute a QM-targeted theorem-gap rework tranche for ROW-PILLAR-QM-001 under the R4 single-row contract so the tranche resolves to either blocker-moving success or explicit fail-closed rework routing.

## Required controls
1. Target row must be ROW-PILLAR-QM-001 and blocker class must be THEOREM_GAP.
2. Success threshold must require negative theorem-gap delta and target-row success evidence.
3. Failure/no-change threshold must route to theorem-gap rework with pinned evidence.
4. Tranche outcome must be materialized in a machine-checkable report.

## Required report pointers
- formal/docs/release/THEOREM_GAP_QM_REWORK_TRANCHE_20260411_v0.json
- formal/output/reports/theorem_gap_qm_rework_tranche_20260411_v0.json

## Governance gate pointer
- formal/python/tests/test_governance_audit_packet_gate.py

## Non-claim boundary
Repository-local QM theorem-gap rework tranche policy only; no scientific adequacy claim.