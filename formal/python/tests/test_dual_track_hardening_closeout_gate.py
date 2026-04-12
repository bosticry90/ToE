from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.tools import dual_track_hardening_closeout as closeout


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload), encoding="utf-8")


def test_dual_track_hardening_closeout_complete_with_valid_inputs(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:

    ledger = tmp_path / "physics_progress_ledger_v0.json"
    cutover = tmp_path / "dual_track_cutover_report_v0.json"
    invalidation = tmp_path / "governance_invalidation_telemetry_v0.json"
    parallel = tmp_path / "governance_parallel_capability_v0.json"

    _write_json(
        ledger,
        {
            "captured_at_utc": "2026-04-11T00:00:00Z",
            "evidence_bundle": {
                "consistency": {
                    "status": "CONSISTENT",
                    "rule": "FAIL_CLOSED_ON_TREND_DELTA_AND_TGC93_ROUTE_CONTRADICTION",
                }
            }
        },
    )
    _write_json(
        cutover,
        {
            "captured_at_utc": "2026-04-11T00:00:00Z",
            "measurement_policy": {
                "measured_mode_required": True,
                "measured_mode_satisfied": True,
            },
            "cutover_readiness": {"overall_pass": True},
        },
    )
    _write_json(
        invalidation,
        {
            "schema_id": "GOVERNANCE_INVALIDATION_TELEMETRY_v0",
            "captured_at_utc": "2026-04-11T00:00:00Z",
            "runs_total": 2,
            "subset_runs": 1,
            "last_run": {"mode": "SUBSET"},
        },
    )
    _write_json(
        parallel,
        {
            "schema_id": "GOVERNANCE_PARALLEL_CAPABILITY_v0",
            "captured_at_utc": "2026-04-11T00:00:00Z",
            "parallel_requested": True,
            "capability_available": True,
            "parallel_activated": True,
        },
    )

    monkeypatch.setattr(closeout, "LEDGER_PATH", ledger)
    monkeypatch.setattr(closeout, "CUTOVER_PATH", cutover)
    monkeypatch.setattr(closeout, "INVALIDATION_TELEMETRY_PATH", invalidation)
    monkeypatch.setattr(closeout, "PARALLEL_CAPABILITY_PATH", parallel)

    payload = closeout.build_closeout(
        captured_at_utc=None,
        max_artifact_age_seconds=999999999,
        min_invalidation_runs=2,
        min_subset_hit_rate_percent=1.0,
    )
    assert payload["summary"]["closeout_status"] == "COMPLETE"
    assert payload["summary"]["all_criteria_satisfied"] is True


def test_dual_track_hardening_closeout_incomplete_when_any_criterion_fails(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:

    ledger = tmp_path / "physics_progress_ledger_v0.json"
    cutover = tmp_path / "dual_track_cutover_report_v0.json"
    invalidation = tmp_path / "governance_invalidation_telemetry_v0.json"
    parallel = tmp_path / "governance_parallel_capability_v0.json"

    _write_json(ledger, {"captured_at_utc": "2026-04-11T00:00:00Z", "evidence_bundle": {"consistency": {"status": "MISSING", "rule": "BAD"}}})
    _write_json(cutover, {"captured_at_utc": "2026-04-11T00:00:00Z", "measurement_policy": {"measured_mode_required": False, "measured_mode_satisfied": False}, "cutover_readiness": {"overall_pass": False}})
    _write_json(invalidation, {"schema_id": "GOVERNANCE_INVALIDATION_TELEMETRY_v0", "captured_at_utc": "2026-04-11T00:00:00Z", "runs_total": 0, "subset_runs": 0, "last_run": {"subset_hit_rate_percent": 0.0}})
    _write_json(parallel, {"schema_id": "GOVERNANCE_PARALLEL_CAPABILITY_v0", "captured_at_utc": "2026-04-11T00:00:00Z", "parallel_requested": True, "capability_available": False, "parallel_activated": False})

    monkeypatch.setattr(closeout, "LEDGER_PATH", ledger)
    monkeypatch.setattr(closeout, "CUTOVER_PATH", cutover)
    monkeypatch.setattr(closeout, "INVALIDATION_TELEMETRY_PATH", invalidation)
    monkeypatch.setattr(closeout, "PARALLEL_CAPABILITY_PATH", parallel)

    payload = closeout.build_closeout(
        captured_at_utc=None,
        max_artifact_age_seconds=999999999,
        min_invalidation_runs=2,
        min_subset_hit_rate_percent=1.0,
    )
    assert payload["summary"]["closeout_status"] == "INCOMPLETE"
    assert payload["summary"]["all_criteria_satisfied"] is False
