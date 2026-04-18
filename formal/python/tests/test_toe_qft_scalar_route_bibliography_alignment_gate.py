from __future__ import annotations

import json
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
ALIGNMENT_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_SCALAR_ROUTE_BIBLIOGRAPHY_ALIGNMENT_v0.md"
REFERENCE_MAP_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_scalar_route_reference_map_v0.json"
MANUSCRIPT_DRAFT_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_SCALAR_ROUTE_MANUSCRIPT_DRAFT_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_toe_qft_scalar_route_bibliography_alignment_doc_has_required_structure() -> None:
    text = _read(ALIGNMENT_DOC_PATH)
    required_strings = [
        "Alignment policy:",
        "Section coverage targets:",
        "Bounded citation posture:",
        "Non-claim boundary:",
        "does not claim interacting-field completion",
        "Reproducibility pointers:",
    ]
    for marker in required_strings:
        assert marker in text, f"Bibliography alignment doc missing marker: {marker}"


def test_toe_qft_scalar_route_reference_map_schema_and_coverage() -> None:
    artifact = _read_json(REFERENCE_MAP_PATH)

    assert artifact.get("artifact_id") == "toe_qft_scalar_route_reference_map_v0"
    assert artifact.get("phase") == "PHASE_3_ROUTE_A_SCALAR_EXTERNAL_BIBLIOGRAPHY_ALIGNMENT"
    assert artifact.get("route_scope") == "bounded_free_scalar_qft_to_qm_bridge"

    categories = artifact.get("reference_categories", [])
    assert "repo_internal_support" in categories
    assert "standard_physics_background" in categories
    assert "interpretive_limitations_context" in categories

    bindings = artifact.get("section_reference_bindings", {})
    required_sections = [
        "motivation_and_scope",
        "master_action_starting_point",
        "scalar_field_derivation",
        "covariance_and_stress_energy",
        "quantization_route",
        "operator_commutator_and_mode_expansion",
        "normalization_and_one_particle_state",
        "nonrelativistic_schrodinger_limit",
        "open_items_and_bounded_claims",
    ]
    assert len(required_sections) == 9
    for section in required_sections:
        assert section in bindings, f"Reference map missing section binding: {section}"
        refs = bindings[section]
        assert isinstance(refs, list) and refs, f"Section has no reference list: {section}"

    refs_catalog = artifact.get("references", {})
    for section, ref_ids in bindings.items():
        for ref_id in ref_ids:
            assert ref_id in refs_catalog, f"Unknown reference id in section {section}: {ref_id}"

    for ref_id, ref in refs_catalog.items():
        category = ref.get("category")
        pointer = ref.get("pointer", "")
        assert category in categories, f"Unknown reference category for {ref_id}: {category}"
        if category == "repo_internal_support":
            path = REPO_ROOT / pointer
            assert path.exists(), f"Repo internal support pointer missing for {ref_id}: {pointer}"
        else:
            assert pointer == "external:placeholder", f"External reference pointer must be placeholder for {ref_id}"

    coverage = artifact.get("coverage", {})
    assert coverage.get("section_count") == 9
    assert coverage.get("all_sections_have_references") is True

    category_coverage = coverage.get("category_coverage", {})
    assert category_coverage.get("repo_internal_support") is True
    assert category_coverage.get("standard_physics_background") is True
    assert category_coverage.get("interpretive_limitations_context") is True

    assert artifact.get("status") == "EXTERNAL_BIBLIOGRAPHY_ALIGNMENT_INTERNAL_EXTERNAL_PLACEHOLDER_MAPPED_v0"


def test_toe_qft_scalar_route_manuscript_has_external_reference_placeholders() -> None:
    text = _read(MANUSCRIPT_DRAFT_PATH)
    required_placeholders = [
        "[REFSEC:motivation_and_scope]",
        "[REFSEC:quantization_route]",
        "[REFSEC:nonrelativistic_schrodinger_limit]",
        "[REFSEC:open_items_and_bounded_claims]",
    ]
    for placeholder in required_placeholders:
        assert placeholder in text, f"Manuscript draft missing external reference placeholder: {placeholder}"
