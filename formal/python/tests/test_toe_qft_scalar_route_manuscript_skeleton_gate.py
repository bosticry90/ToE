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
SKELETON_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_SCALAR_ROUTE_MANUSCRIPT_SKELETON_v0.md"
SECTION_MAP_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_scalar_route_section_map_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_toe_qft_scalar_route_manuscript_skeleton_has_required_structure() -> None:
    text = _read(SKELETON_PATH)
    required_strings = [
        "Section skeleton:",
        "Motivation and scope:",
        "Master-action starting point:",
        "Non-relativistic Schrodinger-class limit:",
        "Open items and bounded claims:",
        "Bounded claim statement:",
        "Non-claim boundary:",
        "does not claim interacting-field completion",
    ]
    for marker in required_strings:
        assert marker in text, f"Manuscript skeleton missing marker: {marker}"


def test_toe_qft_scalar_route_section_map_schema_is_pinned() -> None:
    artifact = _read_json(SECTION_MAP_PATH)

    assert artifact.get("artifact_id") == "toe_qft_scalar_route_section_map_v0"
    assert artifact.get("phase") == "PHASE_3_ROUTE_A_SCALAR_MANUSCRIPT_ASSEMBLY"
    assert artifact.get("route_scope") == "bounded_free_scalar_qft_to_qm_bridge"

    sections = artifact.get("sections", [])
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
    for section in required_sections:
        assert section in sections, f"Section map missing section token: {section}"

    pointers = artifact.get("source_pointers", {})
    assert pointers.get("milestone_summary") == "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_MILESTONE_SUMMARY_v0.md"
    assert pointers.get("nonrelativistic_bridge") == "formal/docs/paper/toe_qft_scalar_nonrelativistic_limit_report_v0.md"

    non_claims = artifact.get("non_claim_boundaries", [])
    assert "no_interacting_field_completion_claim" in non_claims
    assert "no_gauge_sector_completion_claim" in non_claims

    assert artifact.get("status") == "MANUSCRIPT_SKELETON_PINNED_BOUNDED_FREE_SCALAR_QFT_TO_QM_BRIDGE"
