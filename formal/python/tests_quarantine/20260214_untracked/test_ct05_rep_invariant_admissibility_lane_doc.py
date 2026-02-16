from __future__ import annotations

from pathlib import Path


def test_ct05_rep_invariant_admissibility_lane_doc_exists_and_pinned_strings() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    doc_relpath = "formal/docs/programs/CT05_rep_invariant_admissibility_class_lane_spec.md"
    doc_path = repo_root / doc_relpath

    assert doc_path.exists(), f"Missing CT-05 spec doc: {doc_relpath}"

    text = doc_path.read_text(encoding="utf-8")
    required_strings = [
        "CT-05",
        "representation invariance",
        "CT-02",
        "CT-03",
        "RL11",
        "positive control",
        "negative control",
        "eps_rep_invariant",
        "eps_bound_residual",
    ]
    for required in required_strings:
        assert required in text, f"CT-05 spec missing: {required}"
