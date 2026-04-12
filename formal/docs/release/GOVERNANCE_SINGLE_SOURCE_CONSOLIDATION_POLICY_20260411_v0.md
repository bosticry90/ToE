# GOVERNANCE_SINGLE_SOURCE_CONSOLIDATION_POLICY_20260411_v0

## Status
- ACTIVE_NONLIVE_NONCLAIM
- Date: 2026-04-11

## Objective
Enforce governance test selection from one authoritative source (manifest) and prohibit secondary text-pinned registries.

## Required controls
1. Governance suite must not maintain a secondary text registry of gate paths.
2. Governance suite must resolve gate selections through governance manifest selector.
3. Governance suite must resolve governance, critical, and integrity manifest groups.
4. Manifest selector output must match manifest expected count/hash under objective-quality checks.

## Required report pointer
- formal/output/reports/governance_single_source_consolidation_20260411_v0.json

## Governance gate pointer
- formal/python/tests/test_governance_audit_packet_gate.py

## Non-claim boundary
Repository-local governance source-of-truth policy only; no scientific adequacy claim.
