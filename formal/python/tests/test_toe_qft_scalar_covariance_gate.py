from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
REPORT_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "toe_qft_scalar_covariance_report_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_scalar_stress_energy_artifact_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_toe_qft_scalar_covariance_report_has_required_structure() -> None:
    text = _read(REPORT_PATH)
    required_strings = [
        "Covariance statement",
        "Lorentz scalar field",
        "Klein-Gordon class",
        "Canonical stress-energy structure",
        "Assumptions:",
        "Non-claim boundary:",
        "does not claim quantization completion",
    ]
    for marker in required_strings:
        assert marker in text, f"Covariance report missing marker: {marker}"


def test_toe_qft_scalar_stress_energy_artifact_schema_is_pinned() -> None:
    artifact = _read_json(ARTIFACT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_scalar_stress_energy_artifact_v0"
    assert artifact.get("phase") == "PHASE_2_RELATIVISTIC_COVARIANCE"
    assert artifact.get("source") == "master_action_scalar_slice"

    covariance = artifact.get("covariance", {})
    assert covariance.get("field_type") == "lorentz_scalar"
    assert covariance.get("kg_class_consistency") is True

    stress_energy = artifact.get("stress_energy", {})
    assert "canonical_tensor" in stress_energy
    assert "symmetric_tensor" in stress_energy
    assert "energy_density_component" in stress_energy

    assumptions = artifact.get("assumptions", [])
    assert "flat_lorentz_metric_eta" in assumptions
    assert "smooth_field_and_boundary_decay" in assumptions

    assert artifact.get("status") == "PINNED_PHASE2_COVARIANCE_AND_STRESS_ENERGY_ROUTE"
