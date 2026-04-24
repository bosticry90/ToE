from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
PAPER_DIR = REPO_ROOT / "formal" / "docs" / "paper"
REGISTRY_PATH = PAPER_DIR / "PILLAR_DISCHARGE_REGISTRY_v0.json"
COSMO_TARGET_PATH = PAPER_DIR / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = PAPER_DIR / "PHYSICS_ROADMAP_v0.md"
RESULTS_PATH = PAPER_DIR / "RESULTS_TABLE_v0.md"

GENERIC_COMPLETION_GATE_PATH = "formal/python/tests/test_pillar_full_discharge_completion_mechanics.py"
COSMO_CRITERIA_GATE_PATH = "formal/python/tests/test_cosmo_background_full_discharge_adjudication_criteria_artifact.py"
COSMO_AUTH_PACKET_GATE_PATH = "formal/python/tests/test_cosmo_full_derivation_exit_row_authorization_packet_gate.py"
COSMO_READINESS_GATE_PATH = "formal/python/tests/test_cosmo_full_derivation_exit_row_readiness_gate.py"
COSMO_REGISTRY_PATH = "formal/docs/paper/PILLAR_DISCHARGE_REGISTRY_v0.json"
COSMO_CRITERIA_ARTIFACT_PATH = "formal/output/cosmo_background_full_discharge_adjudication_criteria_cycle01_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _find_cosmo_registry_entry(registry: dict) -> dict:
    matches = [entry for entry in registry.get("pillars", []) if entry.get("pillar_key") == "COSMO"]
    assert len(matches) == 1, "Registry must contain exactly one COSMO pillar entry."
    return matches[0]


def test_cosmo_completion_mechanics_is_registry_driven_and_generic_gate_pinned() -> None:
    registry = _read_json(REGISTRY_PATH)
    cosmo_entry = _find_cosmo_registry_entry(registry)

    assert cosmo_entry["pillar_name"] == "PILLAR-COSMO"
    assert cosmo_entry["discharge_doc_path"] == "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md"
    assert cosmo_entry["discharge_adjudication_token"] == "COSMO_BACKGROUND_ADJUDICATION"
    assert cosmo_entry["required_results_rows"] == ["TOE-COSMO-DER-01", "TOE-COSMO-DER-02"]
    assert cosmo_entry["required_theorem_surfaces"], "COSMO registry entry must pin required theorem surfaces."
    assert cosmo_entry["lean_paths"] == ["formal/toe_formal/ToeFormal/Cosmology/BackgroundObjectScaffold.lean"]

    for path in [COSMO_TARGET_PATH, STATE_PATH, ROADMAP_PATH, RESULTS_PATH]:
        text = _read(path)
        assert (
            GENERIC_COMPLETION_GATE_PATH in text
        ), f"{path} must reference the registry-driven generic completion gate `{GENERIC_COMPLETION_GATE_PATH}`."
        assert COSMO_REGISTRY_PATH in text, f"{path} must reference `{COSMO_REGISTRY_PATH}`."
        assert (
            COSMO_CRITERIA_GATE_PATH in text
        ), f"{path} must reference the COSMO criteria gate `{COSMO_CRITERIA_GATE_PATH}`."
        assert (
            COSMO_AUTH_PACKET_GATE_PATH in text
        ), f"{path} must reference the COSMO authorization packet gate `{COSMO_AUTH_PACKET_GATE_PATH}`."
        assert (
            COSMO_READINESS_GATE_PATH in text
        ), f"{path} must reference the COSMO readiness gate `{COSMO_READINESS_GATE_PATH}`."
        assert (
            COSMO_CRITERIA_ARTIFACT_PATH in text
        ), f"{path} must reference the COSMO criteria artifact `{COSMO_CRITERIA_ARTIFACT_PATH}`."
