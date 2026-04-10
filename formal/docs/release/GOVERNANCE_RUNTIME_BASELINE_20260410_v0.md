# GOVERNANCE_RUNTIME_BASELINE_20260410_v0

## Status
- ACTIVE
- Date: 2026-04-10
- Class: RUNTIME_BASELINE_CAPTURE_NONCLAIM

## Objective
Pin measured governance, branch-health, and checkpoint-ladder runtime baselines as machine-readable inputs for the governance audit packet.

## Runtime report pointer
- formal/output/reports/governance_runtime_baseline_20260410_v0.json

## Required metrics
1. governance suite runtime seconds baseline
2. branch-health full pytest runtime seconds baseline
3. checkpoint ladder runtime seconds baseline

## Capture tool
- formal/python/tools/governance_runtime_baseline_capture.py

## Non-claim boundary
This runtime baseline is an operational timing artifact and does not assert scientific adequacy.
