from __future__ import annotations

from pathlib import Path


def test_ct09_independent_external_anchor_plan_doc_exists_and_pinned_strings() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    doc_relpath = "formal/docs/programs/CT09_independent_external_anchor_plan_v0.md"
    doc_path = repo_root / doc_relpath

    assert doc_path.exists(), f"Missing CT-09 plan doc: {doc_relpath}"

    text = doc_path.read_text(encoding="utf-8")
    required_strings = [
        "CT-09",
        "Historical planning artifact retained post-implementation",
        "Planned (not implemented)",
        "truly independent external dataset",
        "not be a slice, transform, or repackaging of CT-06 source rows",
        "Deterministic front-door report generation",
        "Positive control and negative control",
        "explicit break detection",
        "no external truth claim",
    ]
    for required in required_strings:
        assert required in text, f"CT-09 plan doc missing: {required}"


def test_ct09_intake_scaffold_exists_and_is_non_claiming() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    readme_relpath = "formal/external_evidence/ct09_independent_external_anchor_tbd/README.md"
    readme_path = repo_root / readme_relpath
    metadata_template_relpath = "formal/external_evidence/ct09_independent_external_anchor_tbd/dataset_metadata.template.json"
    metadata_template_path = repo_root / metadata_template_relpath

    assert readme_path.exists(), f"Missing CT-09 intake README: {readme_relpath}"
    assert metadata_template_path.exists(), f"Missing CT-09 metadata template: {metadata_template_relpath}"

    text = readme_path.read_text(encoding="utf-8")
    required_strings = [
        "Planning scaffold only",
        "independence documentation",
        "No comparator claims are permitted",
    ]
    for required in required_strings:
        assert required in text, f"CT-09 intake README missing: {required}"
