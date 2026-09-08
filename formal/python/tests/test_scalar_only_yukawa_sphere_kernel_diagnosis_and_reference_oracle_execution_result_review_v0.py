from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_oracle_execution_result_review_v0
    as review,
)


ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = ROOT / review.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_review_regenerates_and_freezes_execution_custody() -> None:
    assert review.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == review.VERDICT
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_execution_artifacts"]
    } == review.EXECUTION_HASHES


def test_review_accepts_24_gates_with_one_provenance_qualification() -> None:
    report = _report()
    summary = report["review_gate_summary"]
    assert summary == {
        "fail": 0,
        "pass": 23,
        "pass_with_qualification": 1,
        "total": 24,
    }
    assert all(
        row["status"] in {"PASS", "PASS_WITH_QUALIFICATION"}
        for row in report["review_gates"]
    )


def test_canonical_copies_and_only_timeout_outputs_are_present() -> None:
    custody = _report()["independent_custody_reproduction"]
    assert custody["canonical_result_copies_equal"] is True
    assert custody["output_files"] == [
        review.OUTPUT_RESULT_RELATIVE_PATH,
        review.TIMEOUT_RELATIVE_PATH,
    ]
    assert custody["matching_execution_process_count"] == 0


def test_timeout_provenance_limitation_is_explicit() -> None:
    custody = _report()["independent_custody_reproduction"]
    assert custody["raw_launcher_transcript_persisted"] is False
    assert custody["exact_child_kill_timestamp_persisted"] is False
    assert custody["timeout_provenance_disposition"] == (
        "ACCEPTED_WITH_RAW_LOG_AND_EXACT_KILL_TIME_LIMITATION"
    )
    assert custody["orphan_process_disposition"] == (
        "RECORDED_EXECUTION_ENGINE_DEFECT_NO_SCIENTIFIC_OUTPUT_ACCEPTED"
    )


def test_accepted_scientific_result_remains_narrow() -> None:
    accepted = _report()["accepted_result"]
    assert accepted == {
        "analytic_oracle": "NOT_QUALIFIED_OR_REFUTED",
        "cause_of_stage_a_failure": "UNRESOLVED",
        "dft_root_cause": "NOT_DETERMINED",
        "principal_outcome": "REFERENCE_ORACLE_INADEQUATE",
        "production_cubature": "NOT_ADJUDICATED",
        "scientific_diagnosis_completed": False,
        "scientific_meaning": "REFERENCE_SYSTEM_NOT_QUALIFIED_WITHIN_FROZEN_WORK_BUDGET",
    }


def test_no_partial_science_or_production_judgment_is_accepted() -> None:
    scope = _report()["scope"]
    assert scope["partial_scientific_values_accepted"] is False
    assert scope["production_method_judgment_accepted"] is False
    assert scope["execution_result_accepted"] is True
    assert scope["one_execution_consumed"] is True


def test_all_downstream_authorities_remain_closed() -> None:
    scope = _report()["scope"]
    for key in (
        "diagnosis_rerun_authorized",
        "kernel_replacement_authorized",
        "stage_a_reopened",
        "jacobian_or_identifiability_authorized",
        "stage_b_authorized",
        "automatic_analytic_oracle_packet_authorized",
    ):
        assert scope[key] is False, key


def test_only_a_fresh_selector_is_authorized() -> None:
    report = _report()
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == (
        "FRESH_POST_DIAGNOSIS_SCIENTIFIC_RESPONSE_SELECTOR_ONLY"
    )
    assert report["scope"]["fresh_scientific_response_selector_authorized"] is True


def test_atomic_and_timeout_finalizer_gates_pass() -> None:
    gates = {row["gate_id"]: row for row in _report()["review_gates"]}
    assert gates["R13_ATOMIC_SCIENTIFIC_WRITER"]["status"] == "PASS"
    assert gates["R14_TIMEOUT_FINALIZER_NONSCIENTIFIC"]["status"] == "PASS"
    assert gates["R15_NO_PARTIAL_SALVAGE"]["status"] == "PASS"


def test_human_review_documents_verdict_and_qualification() -> None:
    human = (ROOT / review.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    assert review.VERDICT in human
    assert "ACCEPTED_WITH_RAW_LOG_AND_EXACT_KILL_TIME_LIMITATION" in human
    assert "RECORDED_EXECUTION_ENGINE_DEFECT_NO_SCIENTIFIC_OUTPUT_ACCEPTED" in human
    assert review.SELECTED_NEXT_TARGET in human

