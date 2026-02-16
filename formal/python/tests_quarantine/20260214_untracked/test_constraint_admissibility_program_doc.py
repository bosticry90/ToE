from __future__ import annotations

from pathlib import Path


def test_constraint_admissibility_program_doc_exists_and_pinned_strings() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    doc_relpath = "formal/docs/programs/CONSTRAINT_ADMISSIBILITY_PROGRAM_v0.md"
    doc_path = repo_root / doc_relpath

    assert doc_path.exists(), f"Missing constraint program doc: {doc_relpath}"

    text = doc_path.read_text(encoding="utf-8")
    required_strings = [
        "Constraint Admissibility Program v0",
        "Bound constraints",
        "Invariance constraints",
        "Stability constraints",
        "Causality/locality constraints",
        "schema",
        "config_tag",
        "regime_tag",
        "domain_tag",
        "positive_control",
        "negative_control",
        "within_rep_only",
        "front_door_only",
        "external_anchor_only",
        "No external truth claim",
    ]
    for required in required_strings:
        assert required in text, f"Constraint program doc missing: {required}"
