from __future__ import annotations

import pytest

from formal.python.tools.repository_dirty_main_terminal_custody_disposition_v0 import (
    classify_path,
)


@pytest.mark.parametrize(
    ("path", "status", "expected"),
    [
        (
            "MAXWELL_DIRAC_ROBUSTNESS_SUMMARY.md",
            " D",
            "HISTORICAL_CUSTODY_ONLY",
        ),
        ("README.md", " M", "PRESERVED_NONCURRENT_RESEARCH"),
        (
            "formal/data/eotwash_2020_primary_evidence_acquisition_v0/a.pdf",
            "??",
            "PRESERVED_EXECUTION_EVIDENCE",
        ),
        (
            "formal/output/example/result.json",
            "??",
            "PRESERVED_EXECUTION_EVIDENCE",
        ),
        (
            "formal/docs/release/LOCAL_SELECTOR_v0.json",
            "??",
            "HISTORICAL_CUSTODY_ONLY",
        ),
        (
            "formal/docs/lanes/EXPLORATORY_PACKET_v0.md",
            "??",
            "PRESERVED_NONCURRENT_RESEARCH",
        ),
        (
            "formal/docs/paper/section.tex",
            "??",
            "PRESERVED_NONCURRENT_RESEARCH",
        ),
        (
            "formal/python/tests/test_unenrolled_lane.py",
            "??",
            "PRESERVED_NONCURRENT_RESEARCH",
        ),
        (
            "formal/python/tools/unenrolled_lane.py",
            "??",
            "PRESERVED_NONCURRENT_RESEARCH",
        ),
        (
            "formal/toe_formal/ToeFormal/Derivation/Unenrolled.lean",
            "??",
            "PRESERVED_NONCURRENT_RESEARCH",
        ),
    ],
)
def test_reviewed_path_cohorts_are_terminal(
    path: str, status: str, expected: str
) -> None:
    disposition, rule, rationale = classify_path(path, status)
    assert disposition == expected
    assert rule.endswith("_v0")
    assert rationale


def test_unreviewed_path_fails_closed() -> None:
    with pytest.raises(ValueError, match="no reviewed terminal custody rule"):
        classify_path("unknown/local/path.bin", "??")


def test_deletion_rule_does_not_accept_a_modified_record() -> None:
    with pytest.raises(ValueError, match="no reviewed terminal custody rule"):
        classify_path("PUBLIC_OVERVIEW.md", " M")
