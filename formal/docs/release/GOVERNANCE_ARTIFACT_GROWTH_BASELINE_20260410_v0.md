# GOVERNANCE_ARTIFACT_GROWTH_BASELINE_20260410_v0

## Status
- ACTIVE
- Date: 2026-04-10
- Class: ARTIFACT_GROWTH_BASELINE_NONCLAIM

## Objective
Pin artifact growth baseline counts and require delta snapshots for ongoing audit-packet comparisons.

## Baseline pointer
- formal/output/reports/governance_artifact_growth_baseline_20260410_v0.json

## Snapshot pointer
- formal/output/reports/governance_artifact_growth_snapshot_20260410_v0.json

## Capture tool
- formal/python/tools/governance_artifact_growth_snapshot.py

## Required metrics
1. current json count under formal/output
2. current json count under formal/output/reports
3. delta vs pinned baseline for both counts

## Non-claim boundary
Artifact growth tracking is an operational repository metric and does not assert scientific adequacy.
