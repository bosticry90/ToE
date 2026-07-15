from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_canonical_execution_v2
    as execution,
)


def test_frozen_inventory_and_record_hashes_are_exact() -> None:
    packet = execution.load_json(execution.REPO_ROOT / execution.V2_PACKET)
    matrix = execution.load_json(execution.REPO_ROOT / execution.V2_MATRIX)
    identity = execution.load_json(execution.REPO_ROOT / execution.V2_IDENTITY)
    audit = execution._identity_audit(packet, matrix, identity)
    assert audit == {
        "scientific_records": 182,
        "positive_controls": 8,
        "negative_controls": 13,
        "total_records": 203,
        "unique_run_ids": 203,
        "unique_casefold_paths": 203,
    }
    assert all(execution._record_input_hash(record) == record["input_hash"] for record in matrix["records"])


def test_registered_series_adds_only_transparent_convergence_aliases() -> None:
    result = {
        "series_numeric": {
            "phi2_l2": [3.0, 5.0],
            "phi3_l2": [4.0, 12.0],
            "time": [0.0, 1.0],
        }
    }
    series = execution._registered_series(result)
    assert series["phi2_l2"] == [3.0, 5.0]
    assert series["phi3_l2"] == [4.0, 12.0]
    assert series["final_phi2_l2"] == [5.0]
    assert series["final_descendant_l2"] == [13.0]


def test_sanitizer_removes_external_decision_fields_recursively() -> None:
    value = {
        "round_trip_passed": True,
        "execution_status": "PASS",
        "evidence": {"row_passed": True, "raw_value": 2.0},
    }
    assert execution._sanitize(value) == {"evidence": {"raw_value": 2.0}}


def test_negative_control_mutations_have_exact_frozen_diagnostics() -> None:
    matrix = execution.load_json(execution.REPO_ROOT / execution.V2_MATRIX)
    controls = [record for record in matrix["records"] if record["run_role"] == "NEGATIVE_CONTROL"]
    assert len(controls) == 13
    for record in controls:
        control_id = record["control_metadata"]["control_id"]
        fixture = execution.numerical.EXPECTED_CONTROL_CONFIG.copy()
        fixture.update(execution.CONTROL_CONFIG_MUTATIONS[control_id])
        diagnostics = [
            execution.DIAGNOSTIC_TRANSLATION.get(item, item)
            for item in execution.numerical.control_diagnostics(fixture)
        ]
        assert diagnostics == [record["control_metadata"]["expected_diagnostic"]]


def test_preflight_or_completed_execution_is_fail_closed(monkeypatch: pytest.MonkeyPatch) -> None:
    required = {"PYTHONHASHSEED": "0", "TZ": "UTC", "LC_ALL": "C", "LANG": "C"}
    for key, value in required.items():
        monkeypatch.setenv(key, value)
    if execution.OUTPUT_ROOT.exists():
        verified = execution.verify_existing_execution()
        assert verified["record_count"] == 203
        with pytest.raises(ValueError):
            execution.preflight(require_empty_outputs=True)
    else:
        preflight = execution.preflight(require_empty_outputs=True)
        assert preflight["identity"]["total_records"] == 203
        assert preflight["output_destination_empty"] is True


def test_no_canonical_output_exists_without_a_start_marker() -> None:
    if not execution.OUTPUT_ROOT.exists():
        assert not execution.START_MARKER.exists()
        assert not execution.TERMINAL_MARKER.exists()
        return
    assert execution.START_MARKER.is_file()
    assert execution.TERMINAL_MARKER.is_file()
    terminal = json.loads(execution.TERMINAL_MARKER.read_text(encoding="utf-8"))
    assert terminal["terminal_state"] in {
        "COMPLETE_PENDING_INDEPENDENT_RESULT_REVIEW",
        "CANONICAL_EXECUTION_INTERRUPTED_OR_FAILED",
    }
