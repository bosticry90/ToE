from __future__ import annotations

from pathlib import Path


def test_toe_target_spec_doc_has_pinned_strings() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    doc_relpath = "formal/docs/toe_target_spec_v1.md"
    doc_path = repo_root / doc_relpath

    assert doc_path.exists(), f"Missing ToE target spec doc: {doc_relpath}"

    text = doc_path.read_text(encoding="utf-8")
    required_strings = [
        "TOE-TARGET-SPEC/v1",
        "Locality/causality",
        "Relativity statement",
        "Gravity statement",
        "Quantum statement",
        "Thermodynamic statement",
        "Structural (Lean)",
        "Behavioral (Python)",
        "Empirical anchoring",
        "Cross-domain consistency",
        "Uniqueness/necessity",
    ]
    for required in required_strings:
        assert required in text, f"ToE target spec doc missing: {required}"
