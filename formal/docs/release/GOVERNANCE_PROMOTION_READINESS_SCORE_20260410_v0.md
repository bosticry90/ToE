# GOVERNANCE_PROMOTION_READINESS_SCORE_20260410_v0

## Status
- ACTIVE
- Date: 2026-04-10
- Class: GOVERNANCE_PROMOTION_DECISION_SIGNAL_NONCLAIM

## Objective
Compose runtime, lifecycle, ownership, artifact-growth, and blocker-closure surfaces into one machine-readable promotion-readiness signal.

## Report pointer
- formal/output/reports/governance_promotion_readiness_score_20260410_v0.json

## Required score fields
- readiness score on a 0 to 100 scale
- readiness status class
- explicit status-rule thresholds
- component-level sub-scores
- raw input bundle pointers and values

## Status rule
- READY if score >= 85
- CONDITIONAL if score >= 65 and < 85
- WATCH if score >= 45 and < 65
- BLOCKED if score < 45

## Gate linkage
- formal/python/tests/test_governance_audit_packet_gate.py

## Non-claim boundary
This readiness score is a repository-local governance control signal and does not assert physics or mathematics completeness.
