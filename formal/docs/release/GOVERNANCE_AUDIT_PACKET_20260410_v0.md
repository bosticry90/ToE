# GOVERNANCE_AUDIT_PACKET_20260410_v0

## Status
- ACTIVE
- Date: 2026-04-10
- Class: GOVERNANCE_AND_CLOSURE_DIAGNOSTIC_NONCLAIM

## Objective
Publish a machine-readable governance audit packet that separates artifact growth, evidence growth, and closure growth, while pinning runtime baselines and closure-map blocker surfaces.

## Packet pointer
- formal/output/reports/governance_audit_packet_20260410_v0.json

## Required dimensions
1. artifact growth
2. evidence growth
3. closure growth

## Artifact growth tracking requirements
- artifact growth baseline declaration pointer
- artifact growth baseline report pointer
- artifact growth snapshot report pointer
- artifact growth snapshot tool pointer
- baseline counts for formal/output and formal/output/reports JSON artifacts
- current counts for formal/output and formal/output/reports JSON artifacts
- delta vs baseline for both JSON artifact scopes

## Runtime baseline requirements
- governance suite runtime baseline
- branch-health full pytest runtime baseline
- warning and hard budget thresholds for both runtime lanes

## Artifact lifecycle requirements
- lifecycle policy declaration pointer
- machine-readable policy pointer
- retention policy thresholds
- exemption classes and family rule count
- missing archive-destination count must be zero

## Closure-map requirements
- blocker count by class
- unresolved blocker classes
- row count and row-to-blocker distribution
- seam/theorem source pointers
- row owner assignments for all rows
- owner coverage ratio and missing-row list
- blocker-to-closure declaration pointer
- blocker-to-closure report pointer
- blocker class plus owning row/lane per map row
- required closure artifact and exit criterion per map row

## Gate hook
- formal/python/tests/test_governance_audit_packet_gate.py

## Non-claim boundary
This packet is a repository-local control artifact and does not assert physics or mathematics completeness.
