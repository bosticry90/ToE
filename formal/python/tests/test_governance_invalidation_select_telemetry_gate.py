from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools.governance_invalidation_select import (
    _select_subset,
    _update_telemetry,
)


def test_invalidation_select_supports_bounded_non_test_family_subset() -> None:
    governance_tests = {
        "formal/python/tests/test_governance_audit_packet_gate.py",
    }
    changed_files = {
        "formal/docs/release/GOVERNANCE_BLOCKER_TREND_WINDOW_20260410_v0.md",
    }

    mode, subset_tests, reasons = _select_subset(changed_files, governance_tests)

    assert mode == "SUBSET"
    assert subset_tests == ["formal/python/tests/test_governance_audit_packet_gate.py"]
    assert "bounded_non_test_family_subset_selected" in reasons


def test_invalidation_select_falls_back_full_for_unmapped_non_test_change() -> None:
    governance_tests = {
        "formal/python/tests/test_governance_audit_packet_gate.py",
    }
    changed_files = {
        "formal/docs/paper/SOME_UNMAPPED_FILE.md",
    }

    mode, subset_tests, reasons = _select_subset(changed_files, governance_tests)

    assert mode == "FULL"
    assert subset_tests == []
    assert reasons == ["non_test_change_outside_bounded_mapping"]


def test_invalidation_telemetry_updates_hit_rate_and_reason_counters(tmp_path: Path) -> None:
    telemetry_path = tmp_path / "telemetry.json"

    _update_telemetry(
        telemetry_path,
        mode="SUBSET",
        reasons=["test_change_subset_selected"],
        selected_count=3,
        changed_count=2,
    )
    _update_telemetry(
        telemetry_path,
        mode="FULL",
        reasons=["non_test_change_outside_bounded_mapping"],
        selected_count=0,
        changed_count=5,
    )

    payload = json.loads(telemetry_path.read_text(encoding="utf-8"))
    assert payload["schema_id"] == "GOVERNANCE_INVALIDATION_TELEMETRY_v0"
    assert payload["runs_total"] == 2
    assert payload["subset_runs"] == 1
    assert payload["full_runs"] == 1
    assert payload["reason_counters"]["test_change_subset_selected"] == 1
    assert payload["reason_counters"]["non_test_change_outside_bounded_mapping"] == 1
    assert payload["last_run"]["mode"] == "FULL"
    assert payload["last_run"]["subset_hit_rate_percent"] == 50.0
