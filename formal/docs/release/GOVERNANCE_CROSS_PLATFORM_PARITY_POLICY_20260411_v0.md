# GOVERNANCE_CROSS_PLATFORM_PARITY_POLICY_20260411_v0

## Status
- ACTIVE_NONLIVE_NONCLAIM
- Date: 2026-04-11

## Objective
Enforce bounded cross-platform parity for governance-critical execution paths by requiring Linux execution of manifest-selected critical and integrity gates.

## Required controls
1. Linux governance parity lane must exist in CI and run on ubuntu-latest.
2. Linux lane must resolve critical and integrity gate sets from governance manifest.
3. Linux lane must execute both resolved gate sets.
4. Parity scope must meet minimum bounded surface size for objective-quality readiness.

## Required report pointer
- formal/output/reports/governance_cross_platform_parity_20260411_v0.json

## Governance gate pointer
- formal/python/tests/test_governance_audit_packet_gate.py

## Non-claim boundary
Repository-local cross-platform parity policy only; no scientific adequacy claim.
