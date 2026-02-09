from __future__ import annotations

from pathlib import Path


def test_relativistic_limit_dispersion_lane_doc_exists() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    doc_relpath = "formal/docs/relativistic_limit_dispersion_lane_spec.md"
    doc_path = repo_root / doc_relpath

    assert doc_path.exists(), f"Missing lane spec doc: {doc_relpath}"

    text = doc_path.read_text(encoding="utf-8")
    required_strings = [
        "COMP-REL-DISP-01/v1",
        "relativistic-form dispersion",
        "representation-eligible",
        "factor-through `.val`",
    ]
    for required in required_strings:
        assert required in text, f"Lane spec doc missing: {required}"
