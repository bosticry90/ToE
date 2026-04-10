# GOVERNANCE_FRESHNESS_SNAPSHOT_20260410_v0

## Status
- ACTIVE
- Date: 2026-04-10
- Class: GOVERNANCE_INPUT_FRESHNESS_POLICY_NONCLAIM

## Objective
Enforce recency budgets for governance inputs so stale reports invalidate readiness-based promotion decisions.

## Report pointer
- formal/output/reports/governance_freshness_snapshot_20260410_v0.json

## Required freshness inputs
- governance runtime baseline report
- artifact growth snapshot report
- blocker-to-closure map report
- promotion-readiness score report
- promotion-action policy report

## Policy
- maximum input age: 86400 seconds
- stale-input effect: readiness invalid and promotion not eligible
- freshness status must be FRESH for promotion-eligibility from freshness to be true

## Gate linkage
- formal/python/tests/test_governance_audit_packet_gate.py

## Non-claim boundary
This freshness policy is a repository-local governance control artifact and does not assert physics or mathematics completeness.
