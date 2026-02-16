from __future__ import annotations

from pathlib import Path


def test_ct10_selection_filter_doc_exists_and_pinned_strings() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    doc_relpath = "formal/docs/programs/CT10_independent_external_anchor_selection_filter_v0.md"
    doc_path = repo_root / doc_relpath

    assert doc_path.exists(), f"Missing CT-10 selection filter doc: {doc_relpath}"

    text = doc_path.read_text(encoding="utf-8")
    required_strings = [
        "CT-10",
        "selection filter",
        "admission gate",
        "truly independent",
        "different observable surface",
        "not BEC-derived",
        "source lineage independence",
        "no shared preprocessing lineage",
        "external_anchor_only",
        "blocked-on-missing",
        "no external truth claim",
        "No comparator claims are permitted",
    ]
    for required in required_strings:
        assert required in text, f"CT-10 selection filter doc missing: {required}"


def test_ct10_intake_scaffold_exists_and_is_non_claiming() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    readme_relpath = "formal/external_evidence/ct10_independent_external_anchor_tbd/README.md"
    readme_path = repo_root / readme_relpath
    metadata_template_relpath = (
        "formal/external_evidence/ct10_independent_external_anchor_tbd/dataset_metadata.template.json"
    )
    metadata_template_path = repo_root / metadata_template_relpath

    assert readme_path.exists(), f"Missing CT-10 intake README: {readme_relpath}"
    assert metadata_template_path.exists(), (
        f"Missing CT-10 metadata template: {metadata_template_relpath}"
    )

    readme_text = readme_path.read_text(encoding="utf-8")
    for required in [
        "Planning scaffold only",
        "independence documentation",
        "not BEC-derived",
        "No comparator claims are permitted",
    ]:
        assert required in readme_text, f"CT-10 intake README missing: {required}"

    template_text = metadata_template_path.read_text(encoding="utf-8")
    for required in [
        "\"schema\": \"CT-10/independent_external_anchor_dataset_metadata/template_v0\"",
        "\"is_bec_derived\": false",
        "Planning scaffold only",
        "No comparator claims are permitted",
    ]:
        assert required in template_text, f"CT-10 metadata template missing: {required}"


def test_ct10_selection_filter_is_wired_into_program_and_state_inventory() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    ct_program = repo_root / "formal/docs/programs/CONDITIONAL_THEOREMS_PROGRAM_v0.md"
    state_doc = repo_root / "State_of_the_Theory.md"

    ct_program_text = ct_program.read_text(encoding="utf-8")
    for required in [
        "CT-10 (pre-activation selection filter)",
        "schema=CT-10",
        "admission gate only",
        "blocked-on-missing",
        "CT10_independent_external_anchor_selection_filter_v0.md",
    ]:
        assert required in ct_program_text, f"CT program doc missing CT-10 wiring: {required}"

    state_text = state_doc.read_text(encoding="utf-8")
    for required in [
        "GapID: COMP-CT-10-FILTER",
        "CT-10 independent external-anchor selection filter v0",
        "CT10_independent_external_anchor_selection_filter_v0.md",
    ]:
        assert required in state_text, f"State inventory missing CT-10 filter entry: {required}"
