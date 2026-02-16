from __future__ import annotations

import re
from pathlib import Path


EXPECTED_SUITE_STATUS_LINE = "Suite status: governance suite green on 2026-02-12 (383 passed)."


def test_conditional_theorems_program_doc_exists_and_pinned_strings() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    doc_relpath = "formal/docs/programs/CONDITIONAL_THEOREMS_PROGRAM_v0.md"
    doc_path = repo_root / doc_relpath

    assert doc_path.exists(), f"Missing CT program doc: {doc_relpath}"

    text = doc_path.read_text(encoding="utf-8")
    required_strings = (
        "Conditional Theorems Program v0",
        "CT-01",
        "CT-06",
        "CT-07",
        "CT-08",
        "CT-09",
        "assumptions",
        "claim",
        "controls",
        "positive control",
        "negative control",
        "expectation-aware",
        "no external truth claim",
        "pinned artifacts",
        "lock file",
        "front door",
        "comparator",
        "RL05",
        "RL11",
        "schema=CT-01",
        "schema=CT-06",
        "schema=CT-07",
        "schema=CT-08",
        "external anchor",
        "dispersion",
        "dataset_id",
        "low-k slice",
        "high-k slice",
        "non_independent_of_CT06",
        "independent external anchor",
        "distance_um_vs_time_ms",
        "Suite status: governance suite green on",
    )
    for required in required_strings:
        assert required in text, f"CT program doc missing: {required}"

    suite_status_matches = re.findall(
        r"Suite status: governance suite green on \d{4}-\d{2}-\d{2} \(\d+ passed\)\.",
        text,
    )
    assert len(suite_status_matches) == 1, (
        "CT program doc must contain exactly one canonical suite-status line with date/pass count."
    )
    assert suite_status_matches[0] == EXPECTED_SUITE_STATUS_LINE, (
        "CT program doc suite-status line drifted from the canonical pinned value."
    )


