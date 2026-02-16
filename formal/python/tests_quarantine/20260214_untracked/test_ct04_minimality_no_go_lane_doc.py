from __future__ import annotations

from pathlib import Path


def test_ct04_minimality_no_go_lane_doc_exists_and_pinned_strings() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    doc_relpath = "formal/docs/programs/CT04_minimality_no_go_lane_spec.md"
    doc_path = repo_root / doc_relpath

    assert doc_path.exists(), f"Missing CT-04 spec doc: {doc_relpath}"

    text = doc_path.read_text(encoding="utf-8")
    required_strings = [
        "CT-04",
        "no-go",
        "minimality",
        "positive control",
        "negative control",
        "cfl_max",
        "constraint_removed",
    ]
    for required in required_strings:
        assert required in text, f"CT-04 spec missing: {required}"
