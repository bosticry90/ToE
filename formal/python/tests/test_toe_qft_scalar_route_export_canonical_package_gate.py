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
NOTE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_SCALAR_ROUTE_EXPORT_CANONICAL_PACKAGE_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_scalar_route_export_canonical_package_checkpoint_v0.json"
EXPORT_ROOT = REPO_ROOT / "formal" / "docs" / "submission" / "scalar_paper1"
MAIN_TEX_PATH = EXPORT_ROOT / "main.tex"
REFS_PATH = EXPORT_ROOT / "refs.bib"
METADATA_PATH = EXPORT_ROOT / "metadata.json"
FIGURES_DIR = EXPORT_ROOT / "figures"
MANUSCRIPT_DRAFT_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_SCALAR_ROUTE_MANUSCRIPT_DRAFT_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_toe_qft_scalar_export_note_has_required_structure() -> None:
    text = _read(NOTE_PATH)
    required_strings = [
        "Canonical export package pointers:",
        "Export-governance checks:",
        "Canonical manuscript presence:",
        "Bibliography presence:",
        "Figure package placeholder presence:",
        "Title and abstract placeholders:",
        "Bounded claim language parity:",
        "Physical contribution representation:",
        "Authority surface mirroring:",
        "Seam hold continuity:",
        "SCALAR_ROUTE_EXPORT_CANONICAL_PACKAGE_STATUS_v0: CANONICAL_SCALAR_PAPER1_EXPORT_OBJECT_PINNED",
    ]
    for marker in required_strings:
        assert marker in text, f"Export canonical package note missing marker: {marker}"


def test_toe_qft_scalar_export_checkpoint_schema_is_pinned() -> None:
    artifact = _read_json(CHECKPOINT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_scalar_route_export_canonical_package_checkpoint_v0"
    assert artifact.get("phase") == "PHASE_3_ROUTE_A_SCALAR_CANONICAL_EXPORT_PACKAGE"
    assert artifact.get("scope") == "bounded_free_scalar_paper1_canonical_single_source_export"

    export_package = artifact.get("export_package", {})
    assert export_package.get("package_root") == "formal/docs/submission/scalar_paper1"
    assert export_package.get("canonical_manuscript") == "formal/docs/submission/scalar_paper1/main.tex"
    assert export_package.get("bibliography") == "formal/docs/submission/scalar_paper1/refs.bib"
    assert export_package.get("metadata") == "formal/docs/submission/scalar_paper1/metadata.json"
    assert export_package.get("figures_dir") == "formal/docs/submission/scalar_paper1/figures"

    checks = artifact.get("gate_checks", {})
    assert checks.get("canonical_tex_manuscript_exists") is True
    assert checks.get("bibliography_exists") is True
    assert checks.get("figure_package_placeholder_exists") is True
    assert checks.get("title_abstract_placeholders_present") is True
    assert checks.get("bounded_claim_language_matches_governed_manuscript") is True
    assert checks.get("physical_contribution_section_represented") is True
    assert checks.get("state_and_roadmap_pointers_present") is True
    assert checks.get("seam_hold_unchanged") is True

    guardrails = artifact.get("policy_guardrails", {})
    assert guardrails.get("scalar_paper1_baseline_freeze") is True
    assert guardrails.get("no_new_scalar_tranche_authorized") is True
    assert guardrails.get("single_source_canonical_export") is True
    assert guardrails.get("seam_hold_token") == "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0"

    assert artifact.get("status_token") == "SCALAR_ROUTE_EXPORT_CANONICAL_PACKAGE_STATUS_v0: CANONICAL_SCALAR_PAPER1_EXPORT_OBJECT_PINNED"
    assert artifact.get("status") == "CANONICAL_SCALAR_PAPER1_EXPORT_OBJECT_PINNED"


def test_toe_qft_scalar_export_package_files_and_content_exist() -> None:
    manuscript_text = _read(MAIN_TEX_PATH)

    assert REFS_PATH.exists(), f"Missing bibliography file: {REFS_PATH}"
    assert METADATA_PATH.exists(), f"Missing metadata file: {METADATA_PATH}"
    assert FIGURES_DIR.exists() and FIGURES_DIR.is_dir(), f"Missing figures directory: {FIGURES_DIR}"

    assert "TITLE_PLACEHOLDER_SCALAR_PAPER1" in manuscript_text
    assert "ABSTRACT_PLACEHOLDER_SCALAR_PAPER1" in manuscript_text

    bounded_claim_sentence = (
        "This manuscript claims a governed, bounded free-scalar QFT-to-QM bridge narrative "
        "backed by pinned derivation and manuscript surfaces."
    )
    assert bounded_claim_sentence in manuscript_text
    assert "\\section{Physical Contribution of the Bounded Scalar Result}" in manuscript_text

    governed_manuscript_text = _read(MANUSCRIPT_DRAFT_PATH)
    assert "Bounded claim statement:" in governed_manuscript_text
    assert "This draft claims a governed, bounded free-scalar QFT-to-QM bridge narrative" in governed_manuscript_text


def test_toe_qft_scalar_export_is_mirrored_in_authority_surfaces_and_seam_hold_is_unchanged() -> None:
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    refs = [
        "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_EXPORT_CANONICAL_PACKAGE_v0.md",
        "formal/output/toe_qft_scalar_route_export_canonical_package_checkpoint_v0.json",
        "formal/python/tests/test_toe_qft_scalar_route_export_canonical_package_gate.py",
        "formal/docs/submission/scalar_paper1/main.tex",
        "formal/docs/submission/scalar_paper1/refs.bib",
        "SCALAR_ROUTE_EXPORT_CANONICAL_PACKAGE_STATUS_v0: CANONICAL_SCALAR_PAPER1_EXPORT_OBJECT_PINNED",
        "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0",
    ]

    for ref in refs:
        assert ref in state_text or ref in inventory_text, (
            f"State/Inventory missing scalar export canonical-package ref: {ref}"
        )
        assert ref in roadmap_text, f"Roadmap missing scalar export canonical-package ref: {ref}"
