from __future__ import annotations

from pathlib import Path


def test_comparator_manifest_schema_v2_doc_exists() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    doc_relpath = "formal/docs/comparator_rep_interpretability_manifest_schema_v2.md"
    doc_path = repo_root / doc_relpath

    assert doc_path.exists(), f"Missing schema doc: {doc_relpath}"

    text = doc_path.read_text(encoding="utf-8")
    required_strings = [
        "Toe/comparator_rep_interpretability_manifest/v2",
        "within_rep_only",
        "cross_rep_equivalent",
        "proof_artifact",
        "proof_build_guard_test",
        "policy_token_required_for_cross_rep",
    ]
    for required in required_strings:
        assert required in text, f"Schema doc missing required string: {required}"
