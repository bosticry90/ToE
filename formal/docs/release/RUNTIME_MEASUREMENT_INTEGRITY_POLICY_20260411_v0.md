# RUNTIME_MEASUREMENT_INTEGRITY_POLICY_20260411_v0

## Status
- ACTIVE_NONLIVE_NONCLAIM
- Date: 2026-04-11

## Objective
Require measured-quality runtime evidence before accepting optimization or cutover claims.

## Required controls
1. Baseline runtime artifact must be MEASURED.
2. Current runtime snapshot artifact must be MEASURED.
3. Both artifacts must contain command provenance hashes.
4. Cutover measurement policy must require and satisfy measured mode.
5. Baseline and snapshot artifacts must carry measured sample_count from shared runtime history.
6. Objective-quality runtime evidence requires minimum multi-sample threshold and bounded drift.

## Required report pointer
- formal/output/reports/runtime_measurement_integrity_20260411_v0.json

## Governance gate pointer
- formal/python/tests/test_governance_audit_packet_gate.py

## Non-claim boundary
Repository-local runtime evidence policy only; no scientific adequacy claim.
