from __future__ import annotations

import json
from functools import lru_cache
from pathlib import Path
from typing import Any

import pytest

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_implementation_v0
    as implementation_v0,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_observable_semantics_reconciliation_result_review_v2
    as result_review_v2,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_observable_semantics_reconciliation_v1
    as predecessor_v1,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_observable_semantics_reconciliation_v2
    as reconciliation_v2,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_raw_evidence_assembler_v3
    as raw_v3,
)


ROOT = find_repo_root(Path(__file__))
SOURCE_ROOT = ROOT / result_review_v2.SOURCE_OUTPUT_ROOT_RELATIVE_PATH
RESULT_ROOT = ROOT / reconciliation_v2.RESULT_OUTPUT_ROOT_RELATIVE_PATH


@lru_cache(maxsize=1)
def _raw_review() -> bytes:
    return result_review_v2.artifact_bytes()


@lru_cache(maxsize=1)
def _review() -> dict[str, Any]:
    value = json.loads(_raw_review().decode("utf-8"))
    assert isinstance(value, dict)
    return value


def test_result_review_regenerates_exactly_and_deterministically() -> None:
    raw = _raw_review()
    assert (ROOT / result_review_v2.REPORT_RELATIVE_PATH).read_bytes() == raw
    assert result_review_v2.artifact_bytes() == raw


def test_result_review_never_reads_payload_arrays_or_reenters_calculation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: Any, **_kwargs: Any) -> None:
        raise AssertionError("payload or calculation path entered during result review")

    monkeypatch.setattr(predecessor_v1, "_load_payloads", forbidden)
    monkeypatch.setattr(raw_v3, "_load_role_payload", forbidden)
    monkeypatch.setattr(reconciliation_v2, "build_authorized_comparison", forbidden)
    before = implementation_v0.directory_tree_sha256(SOURCE_ROOT)
    review = result_review_v2.build_review()
    after = implementation_v0.directory_tree_sha256(SOURCE_ROOT)
    assert before == after == reconciliation_v2.EXPECTED_SOURCE_OUTPUT_TREE_SHA256
    checks = review["independent_review_checks"]
    assert checks["actual_payload_arrays_read_during_result_review"] is False
    assert checks["calculation_reentered_during_result_review"] is False
    assert not RESULT_ROOT.exists()


def test_exact_producer_consumer_key_mismatch_is_identified() -> None:
    mismatch = _review()["input_contract_mismatch"]
    assert mismatch["producer_runtime_key"] == "exact_run_ids"
    assert mismatch["producer_runtime_value"] == list(raw_v3.EXPECTED_RUN_IDS)
    assert mismatch["consumer_required_runtime_key"] == "requested_run_ids"
    assert mismatch["consumer_observed_runtime_value"] is None
    assert mismatch["consumer_expected_runtime_value"] == list(raw_v3.EXPECTED_RUN_IDS)
    assert mismatch["raised_result"] == "BLOCKED_CUSTODY"
    assert mismatch["raised_diagnostic"] == "EXECUTION_START_MARKER_INVALID"
    assert mismatch["classification"] == "PRODUCTION_CONSUMER_CONTRACT_MISMATCH"


def test_no_terminal_is_assigned_when_input_validation_is_incomplete() -> None:
    invocation = _review()["calculation_invocation_review"]
    assert invocation["authorized_invocation_count"] == 1
    assert invocation["observed_invocation_count_this_cycle"] == 1
    assert invocation["completed_comparison_count"] == 0
    assert invocation["derived_result_artifact_count"] == 0
    assert invocation["terminal_classification"] == "NOT_ASSIGNED_PRETERMINAL"
    assert invocation["field_count_compared"] == 0
    assert invocation["payload_comparison_completed"] is False
    assert not RESULT_ROOT.exists()


def test_all_ten_read_only_result_review_checks_pass() -> None:
    audit = _review()["independent_review_checks"]
    assert audit["passed_check_count"] == audit["check_count"] == 10
    assert all(audit["checks"].values())


def test_frozen_hard_stop_terminates_lane_without_retry_or_repair() -> None:
    review = _review()
    assert review["verdict"] == (
        "BLOCKED_RECONCILIATION_PRETERMINAL_INPUT_CONTRACT_MISMATCH"
    )
    assert review["first_diagnostic"] == "EXECUTION_START_RUN_ID_KEY_MISMATCH"
    hard_stop = review["hard_stop"]
    assert hard_stop["retry_authorized"] is False
    assert hard_stop["second_calculation_authorized"] is False
    assert hard_stop["packet_v3_authorized"] is False
    assert hard_stop["simulation_authorized"] is False
    assert hard_stop["source_output_rewrite_authorized"] is False
    assert hard_stop["raw_assembler_repair_authorized_in_closed_lane"] is False
    assert hard_stop["reconciliation_lane_terminated"] is True


def test_scientific_claim_ceiling_remains_unchanged() -> None:
    core = _review()["preserved_scientific_core"]
    assert core["fourteen_row_robustness"] == "NUMERICALLY_BLOCKED"
    assert core["descendant_materiality"] == "NOT_EVALUATED_NUMERICAL_BLOCK"
    assert core["H_A_through_H_E"] == "NOT_EVALUATED"
    assert core["R13_root_mechanism"] == "UNRESOLVED_EVIDENCE_SEMANTICS_BLOCK"
    assert core["new_E_REPRO"] == "NONE"
