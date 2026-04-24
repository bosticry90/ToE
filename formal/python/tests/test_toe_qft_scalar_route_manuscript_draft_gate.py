from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
DRAFT_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_SCALAR_ROUTE_MANUSCRIPT_DRAFT_v0.md"
FILL_MAP_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_scalar_route_manuscript_fill_map_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_toe_qft_scalar_route_manuscript_draft_has_required_structure() -> None:
    text = _read(DRAFT_PATH)
    required_strings = [
        "Section drafts:",
        "Motivation and scope:",
        "Master-action starting point:",
        "Non-relativistic Schrodinger-class limit:",
        "Gap-closure pass v1:",
        "Gap-closure pass v2:",
        "Ranked glue gaps (highest-impact first):",
        "Ranked glue gaps for pass v2 (highest-impact first):",
        "Closed in this pass:",
        "Remaining explanatory glue log:",
        "Remaining explanatory glue log (after pass v2):",
        "Citation placeholder: [CIT:motivation_and_scope",
        "Citation placeholder: [CIT:nonrelativistic_schrodinger_limit",
        "External reference placeholder: [REFSEC:motivation_and_scope]",
        "External reference placeholder: [REFSEC:nonrelativistic_schrodinger_limit]",
        "Bounded claim statement:",
        "Non-claim boundary:",
        "does not claim interacting-field completion",
    ]
    for marker in required_strings:
        assert marker in text, f"Manuscript draft missing marker: {marker}"


def test_toe_qft_scalar_route_manuscript_fill_map_schema_is_pinned() -> None:
    artifact = _read_json(FILL_MAP_PATH)

    assert artifact.get("artifact_id") == "toe_qft_scalar_route_manuscript_fill_map_v0"
    assert artifact.get("phase") == "PHASE_3_ROUTE_A_SCALAR_MANUSCRIPT_FILL"
    assert artifact.get("route_scope") == "bounded_free_scalar_qft_to_qm_bridge"

    fill_status = artifact.get("section_fill_status", {})
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
    expected_statuses = {
        "motivation_and_scope": "GAP_CLOSED_v1",
        "master_action_starting_point": "GAP_CLOSED_v1",
        "scalar_field_derivation": "GAP_CLOSED_v1",
        "covariance_and_stress_energy": "GAP_CLOSED_v2",
        "quantization_route": "GAP_CLOSED_v2",
        "operator_commutator_and_mode_expansion": "GAP_CLOSED_v2",
        "normalization_and_one_particle_state": "GAP_CLOSED_v2",
        "nonrelativistic_schrodinger_limit": "GAP_CLOSED_v2",
        "open_items_and_bounded_claims": "GAP_CLOSED_v2",
    }
    for section in required_sections:
        assert fill_status.get(section) == expected_statuses[section], f"Unexpected section fill status for {section}: {fill_status.get(section)}"

    ranked_glue = artifact.get("ranked_glue_gaps", [])
    assert "quantization_mode_normalization_transition_tightening" in ranked_glue
    assert "qft_to_schrodinger_interpretive_bridge_clarity" in ranked_glue

    resolved_glue = artifact.get("resolved_glue_gaps", [])
    assert "covariance_to_quantization_transition_paragraph" in resolved_glue
    assert "notation_harmonization_block_k_omega_low_energy" in resolved_glue
    assert "narrative_redundancy_reduction" in resolved_glue

    remaining_glue = artifact.get("remaining_explanatory_glue", [])
    assert "final_copy_edit_tone_consistency" in remaining_glue

    citation_status = artifact.get("citation_binding_status", {})
    assert citation_status.get("internal_section_bindings") == "ALIGNED_v1"
    assert citation_status.get("external_references") == "ALIGNED_v1"

    non_claims = artifact.get("non_claim_boundaries", [])
    assert "no_interacting_field_completion_claim" in non_claims
    assert "no_gauge_sector_completion_claim" in non_claims

    assert artifact.get("status") == "MANUSCRIPT_FILL_GAP_CLOSURE_PASS4_BIBLIOGRAPHY_ALIGNED_BOUNDED_FREE_SCALAR_QFT_TO_QM_BRIDGE"
