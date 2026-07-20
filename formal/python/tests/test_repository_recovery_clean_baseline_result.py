from __future__ import annotations

from pathlib import Path

from formal.python.tools import repository_recovery_clean_baseline_result as result


def test_dirty_result_is_preserved_not_rerun() -> None:
    assert result.AUDITED_DIRTY_RESULT["rerun"] is False
    assert result.AUDITED_DIRTY_RESULT["status"] == (
        "NOT_RERUN_TO_PRESERVE_AUDITED_WORKTREE"
    )


def test_root_cause_classification_covers_known_committed_defect() -> None:
    classification, paths = result._root_cause(
        "formal/python/tests/test_conftest_signature_stability_gate.py::test_hash",
        "",
    )
    assert classification == "COMMITTED_SOURCE_DEFECT"
    assert "formal/python/tests/conftest.py" in paths


def test_first_exception_extracts_only_reported_evidence() -> None:
    log = """
____________________________ test_hash ____________________________
E   AssertionError: expected approved hash
=========================== short test summary info ===========================
FAILED formal/python/tests/test_gate.py::test_hash - AssertionError
"""
    assert result._first_exception(
        "formal/python/tests/test_gate.py::test_hash", log
    ) == "AssertionError: expected approved hash"
    index = result._exception_index(log)
    assert result._first_exception(
        "formal/python/tests/test_gate.py::test_hash", log, index=index
    ) == "AssertionError: expected approved hash"


def test_first_exception_fails_closed_when_report_is_ambiguous() -> None:
    assert result._first_exception("x.py::test_missing", "no report") == (
        "NOT_EXTRACTED_REQUIRES_RAW_LOG_REVIEW"
    )


def _write_baseline(tmp_path: Path, nodeid: str) -> None:
    test_name = nodeid.rsplit("::", 1)[-1]
    (tmp_path / "full_pytest.log").write_text(
        f"""
____________________________ {test_name} ____________________________
E   AssertionError: preserved failure
=========================== short test summary info ===========================
FAILED {nodeid} - AssertionError
1 failed, 2 passed in 1.00s
""",
        encoding="utf-8",
    )
    (tmp_path / "full_pytest.status.txt").write_text(
        "STARTED=2026-07-19T00:00:00Z\nENDED=2026-07-19T00:00:01Z\nEXIT=1\n",
        encoding="utf-8",
    )


def test_result_requires_every_failure_to_be_classified(tmp_path: Path) -> None:
    _write_baseline(tmp_path, "formal/python/tests/test_unknown_gate.py::test_unknown")
    _, matrix = result.build_result(tmp_path)
    assert matrix["complete_failure_population"] is True
    assert matrix["all_failures_classified"] is False
    assert matrix["rows"][0]["first_exception"] == (
        "AssertionError: preserved failure"
    )


def test_result_accepts_complete_known_failure_classification(tmp_path: Path) -> None:
    _write_baseline(
        tmp_path,
        "formal/python/tests/test_conftest_signature_stability_gate.py::test_hash",
    )
    _, matrix = result.build_result(tmp_path)
    assert matrix["all_failures_classified"] is True
