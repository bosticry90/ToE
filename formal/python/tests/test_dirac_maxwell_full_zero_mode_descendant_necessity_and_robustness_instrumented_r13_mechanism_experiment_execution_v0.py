from __future__ import annotations

import json
from functools import lru_cache
from pathlib import Path
from typing import Any

import pytest

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_execution_v0
    as execution,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_executor_v3
    as executor_v3,
)


ROOT = find_repo_root(Path(__file__))


@lru_cache(maxsize=1)
def _raw() -> bytes:
    return execution.artifact_bytes()


@lru_cache(maxsize=1)
def _report() -> dict[str, Any]:
    value = json.loads(_raw().decode("utf-8"))
    assert isinstance(value, dict)
    return value


def test_execution_receipt_regenerates_exactly_and_deterministically() -> None:
    raw = _raw()
    assert (ROOT / execution.REPORT_RELATIVE_PATH).read_bytes() == raw
    assert execution.artifact_bytes() == raw


def test_exactly_six_runs_and_fourteen_authorized_files_are_preserved() -> None:
    report = _report()
    assert report["execution_status"] == "EXECUTION_COMPLETED_ONCE"
    assert report["execution_invocation_count"] == 1
    assert report["authorized_run_count"] == 6
    assert report["completed_run_count"] == 6
    assert report["role_payload_file_count"] == 12
    assert report["auxiliary_file_count"] == 2
    assert report["total_output_file_count"] == 14
    assert [item["execution_ordinal"] for item in report["execution_order"]] == [
        1,
        2,
        3,
        4,
        5,
        6,
    ]
    assert all(item["executed_exactly_once"] for item in report["execution_order"])
    assert all(
        item["json_bytes_exact"] and item["npz_bytes_exact"]
        for item in report["execution_order"]
    )


def test_anchor_runtime_resolution_and_output_custody_all_pass() -> None:
    report = _report()
    assert report["custody_check_count"] == 13
    assert report["passed_custody_check_count"] == 13
    assert report["failed_custody_check_ids"] == []
    assert all(report["custody_checks"].values())
    runtime = report["runtime_custody_summary"]
    assert runtime["loaded_module_count"] == 8
    assert runtime["read_only_plan_count"] == 6
    assert runtime["simulation_entry_count_at_preflight"] == 0
    assert runtime["execution_invoked"] is True


def test_raw_file_hashes_and_observed_timestamps_are_recorded() -> None:
    report = _report()
    receipts = report["output_file_receipts"]
    assert len(receipts) == 14
    for item in receipts:
        path = ROOT / item["relative_output_path"]
        assert path.is_file()
        assert item["byte_count"] == len(path.read_bytes())
        assert item["sha256"] == execution.sha256_bytes(path.read_bytes())
        assert isinstance(item["filesystem_creation_time_ns"], int)
        assert isinstance(item["filesystem_last_write_time_ns"], int)
        assert item["filesystem_creation_time_utc"].endswith("Z")
        assert item["filesystem_last_write_time_utc"].endswith("Z")
    window = report["observed_execution_timestamp_window"]
    assert window["earliest_creation_time_ns"] <= window["latest_last_write_time_ns"]
    assert window["source"].startswith("local filesystem metadata")


def test_execution_did_not_accept_a_mechanism_or_scientific_result() -> None:
    report = _report()
    classifier = report["classifier_execution"]
    assert classifier["classifier_invoked_by_receipt"] is False
    assert classifier["stored_classifier_metrics_treated_as_authoritative"] is False
    assert classifier["H_A_through_H_E_decided_by_receipt"] is False
    instrumentation = report["instrumentation_execution_facts"]
    assert instrumentation["pair_count"] == 3
    assert instrumentation["all_pairs_byte_identical"] is True
    assert instrumentation["scientific_acceptance_status"] == (
        "PENDING_INDEPENDENT_RESULT_REVIEW"
    )
    preserved = report["preserved_scientific_core"]
    assert preserved["fourteen_row_robustness"] == "NUMERICALLY_BLOCKED"
    assert preserved["R13_root_mechanism"] == "UNRESOLVED"
    assert preserved["new_E_REPRO"] == "NONE"


def test_additional_execution_is_fail_closed_at_read_only_preflight(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    for key, value in execution.load_json(
        execution.REVIEW_RELATIVE_PATH
    )[execution.custody_v3.REVIEW_AUTHORITY_FIELD][
        "runtime_source_closure"
    ].get("required_execution_environment", {}).items():
        monkeypatch.setenv(key, value)
    for key, value in {
        "PYTHONHASHSEED": "0",
        "TZ": "UTC",
        "LC_ALL": "C",
        "LANG": "C",
        "OPENBLAS_NUM_THREADS": "1",
        "OMP_NUM_THREADS": "1",
        "MKL_NUM_THREADS": "1",
        "NUMEXPR_NUM_THREADS": "1",
    }.items():
        monkeypatch.setenv(key, value)
    output_root = ROOT / execution.OUTPUT_ROOT_RELATIVE_PATH
    before = {
        path.name: execution.sha256_bytes(path.read_bytes())
        for path in output_root.iterdir()
        if path.is_file()
    }
    with pytest.raises(
        executor_v3.RuntimeCustodyError,
        match="mechanism output root already exists",
    ):
        executor_v3.preflight_frozen_execution(ROOT)
    after = {
        path.name: execution.sha256_bytes(path.read_bytes())
        for path in output_root.iterdir()
        if path.is_file()
    }
    assert after == before
    assert len(after) == 14


def test_authority_rotates_only_to_independent_result_review() -> None:
    report = _report()
    assert report["verdict"] == (
        "EXECUTION_COMPLETED_ONCE_PENDING_INDEPENDENT_RESULT_REVIEW"
    )
    assert report["selected_next_target"] == execution.SELECTED_NEXT_TARGET
    boundary = report["authority_boundary"]
    assert boundary["execution_completed"] is True
    assert boundary["additional_execution_authorized"] is False
    assert boundary["retry_authorized"] is False
    assert boundary["payload_rewrite_authorized"] is False
    assert boundary["mechanism_result_accepted"] is False
    assert boundary["instrumentation_nonperturbation_result_accepted"] is False
    assert boundary["independent_result_review_required"] is True
