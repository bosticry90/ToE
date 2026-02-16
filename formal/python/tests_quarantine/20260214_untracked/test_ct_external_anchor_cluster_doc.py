from __future__ import annotations

from pathlib import Path


def test_ct_external_anchor_cluster_doc_exists_and_pinned_strings() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    doc_relpath = "formal/docs/programs/CT_external_anchor_cluster_v0.md"
    doc_path = repo_root / doc_relpath

    assert doc_path.exists(), f"Missing CT external-anchor cluster doc: {doc_relpath}"

    text = doc_path.read_text(encoding="utf-8")
    required_strings = [
        "CT-06/CT-07/CT-08",
        "external-anchor evidence family",
        "non_independent_of_CT06",
        "not independent external confirmations",
        "dataset-conditional",
        "expectation-aware controls",
        "Negative control must be explicit break detection",
    ]
    for required in required_strings:
        assert required in text, f"CT external-anchor cluster doc missing: {required}"
