# GOVERNANCE_BLOCKER_TREND_WINDOW_20260410_v0

## Status
- ACTIVE
- Date: 2026-04-10
- Class: GOVERNANCE_BLOCKER_MOVEMENT_POLICY_NONCLAIM

## Objective
Track blocker movement over the active window and enforce exception linkage when blocker reduction does not occur.

## Report pointer
- formal/output/reports/governance_blocker_trend_window_20260410_v0.json

## Required trend fields
- window start/end
- tranche id
- blocker counts prior/current/net delta
- movement status
- movement rule
- exception requirement and exception artifact pointer when required

## Movement rule
- net delta < 0: decreasing (progress)
- net delta >= 0: exception required

## Gate linkage
- formal/python/tests/test_governance_audit_packet_gate.py

## Non-claim boundary
This blocker trend window is a repository-local governance control artifact and does not assert physics or mathematics completeness.
