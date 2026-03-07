# TOE Orchestration Report Contract v0

Status: ACTIVE_v0
Owner: ToE governance
Last updated: 2026-03-06

## Purpose

Pin the canonical report path emitted by async orchestration and the gate that enforces this contract.

## Canonical Paths

- Manifest path: `formal/docs/release/TOE_ASYNC_ORCHESTRATION_MANIFEST_v0.json`
- Canonical report path: `formal/output/reports/toe_orchestration_report_v0.json`
- Report schema path: `formal/docs/release/TOE_ADJUDICATION_REPORT_SCHEMA_v0.json`
- Gate path: `formal/python/tests/test_orchestration_report_contract_gate.py`

## Drift Policy

- Runner defaults must remain aligned with these pinned paths.
- Schema required fields must not be removed.
- Changes require explicit governance update.
