from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
REPORT_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "toe_qft_scalar_nonrelativistic_limit_report_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_scalar_schrodinger_limit_artifact_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_toe_qft_scalar_nonrelativistic_limit_report_has_required_structure() -> None:
    text = _read(REPORT_PATH)
    required_strings = [
        "Non-relativistic bridge hardening",
        "|k| << m",
        "phi(t,x) = exp(-i m t) psi(t,x) / sqrt(2m)",
        "Schrodinger-class limit statement (bounded)",
        "i partial_t psi = -(nabla^2/(2m)) psi",
        "Non-claim boundary:",
        "does not claim interacting-field non-relativistic completion",
    ]
    for marker in required_strings:
        assert marker in text, f"Nonrelativistic report missing marker: {marker}"


def test_toe_qft_scalar_schrodinger_limit_artifact_schema_is_pinned() -> None:
    artifact = _read_json(ARTIFACT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_scalar_schrodinger_limit_artifact_v0"
    assert artifact.get("phase") == "PHASE_3_ROUTE_A_NONRELATIVISTIC_SCHRODINGER_BRIDGE"
    assert artifact.get("source") == "free_scalar_nonrelativistic_bridge_route"

    assumptions = artifact.get("low_energy_assumptions", {})
    assert assumptions.get("momentum_hierarchy") == "|k| << m"
    assert assumptions.get("units") == "c=1"
    assert assumptions.get("positive_frequency_sector_selected") is True

    extraction = artifact.get("phase_extraction", {})
    assert extraction.get("field_decomposition") == "phi(t,x)=exp(-i m t) psi(t,x)/sqrt(2m)"
    assert extraction.get("fast_oscillation_remainder_suppressed") is True
    assert extraction.get("leading_order_envelope_kept") is True

    schrodinger = artifact.get("schrodinger_limit", {})
    assert schrodinger.get("equation") == "i partial_t psi = -(nabla^2/(2m)) psi"
    assert schrodinger.get("order_control") == "leading_order_in_|k|/m"
    assert schrodinger.get("one_particle_posture_bounded") is True

    model_assumptions = artifact.get("assumptions", [])
    assert "free_scalar_regime_only" in model_assumptions
    assert "non_relativistic_expansion_leading_order" in model_assumptions

    assert artifact.get("status") == "PINNED_ROUTE_A_NONRELATIVISTIC_SCHRODINGER_BRIDGE"
