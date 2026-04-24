from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
DRAFT_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_SCALAR_ROUTE_MANUSCRIPT_DRAFT_v0.md"
BINDING_MAP_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_scalar_route_citation_binding_map_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_toe_qft_scalar_route_citation_binding_map_schema_is_pinned() -> None:
    artifact = _read_json(BINDING_MAP_PATH)

    assert artifact.get("artifact_id") == "toe_qft_scalar_route_citation_binding_map_v0"
    assert artifact.get("phase") == "PHASE_3_ROUTE_A_SCALAR_MANUSCRIPT_CITATION_BINDING"
    assert artifact.get("route_scope") == "bounded_free_scalar_qft_to_qm_bridge"

    bindings = artifact.get("section_bindings", {})
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
        assert section in bindings, f"Citation binding missing section: {section}"
        entry = bindings[section]
        assert "placeholder" in entry and entry["placeholder"], f"Citation binding missing placeholder for {section}"
        assert "source_path" in entry and entry["source_path"], f"Citation binding missing source_path for {section}"
        assert "gate_path" in entry and entry["gate_path"], f"Citation binding missing gate_path for {section}"

        source_path = REPO_ROOT / entry["source_path"]
        gate_path = REPO_ROOT / entry["gate_path"]
        assert source_path.exists(), f"Citation source path does not exist for {section}: {entry['source_path']}"
        assert gate_path.exists(), f"Citation gate path does not exist for {section}: {entry['gate_path']}"

    coverage = artifact.get("binding_coverage", {})
    assert coverage.get("section_count") == 9
    assert coverage.get("all_sections_bound") is True

    assert artifact.get("external_reference_status") == "DEFERRED"
    assert artifact.get("status") == "CITATION_BINDING_INTERNAL_TRACEABILITY_ALIGNED_v0"


def test_toe_qft_scalar_route_manuscript_contains_all_citation_placeholders() -> None:
    text = _read(DRAFT_PATH)
    artifact = _read_json(BINDING_MAP_PATH)

    bindings = artifact.get("section_bindings", {})
    for section, entry in bindings.items():
        placeholder = entry["placeholder"]
        assert placeholder in text, f"Manuscript draft missing citation placeholder for {section}: {placeholder}"
