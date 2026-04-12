# THEOREM_GAP_EXECUTION_LINKAGE_20260411_v0

## Status
- ACTIVE_NONLIVE_NONCLAIM
- Date: 2026-04-11

## Objective
Require theorem-gap-facing tranches to declare target row, expected blocker-state change, and evidence pointer so tranche-level success/failure/no-change outcomes are machine-checkable.

## Required controls
1. Each linkage registry entry must include tranche ID, target row, expected blocker-state change, explicit success threshold, actual blocker-state change, outcome status, declaration pointer, and evidence pointer.
2. Each tranche ID must map to exactly one target row (single-target tranche enforcement).
3. Target row must resolve to a theorem-gap row in the canonical closure map.
4. Declaration and evidence pointers must resolve to existing repository files.
5. Any tranche with outcome status NO_CHANGE must declare explicit rework routing and a rework evidence pointer (fail-closed on missing route).
6. Objective completion requires at least one success entry and negative theorem-gap delta.

## Required report pointers
- formal/docs/release/THEOREM_GAP_TRANCHE_LINKAGE_REGISTRY_20260411_v0.json
- formal/output/reports/theorem_gap_execution_linkage_20260411_v0.json

## Governance gate pointer
- formal/python/tests/test_governance_audit_packet_gate.py

## Non-claim boundary
Repository-local theorem-gap execution-accountability policy only; no scientific adequacy claim.