from __future__ import annotations

import json
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
REPORT_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "toe_qft_scalar_field_derivation_report_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_scalar_field_equations_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_toe_qft_scalar_field_report_contains_euler_lagrange_and_kg_mapping() -> None:
    text = _read(REPORT_PATH)
    required_strings = [
        "master action",
        "Euler-Lagrange",
        "box phi + m_eff^2 phi + dV_int/dphi = 0",
        "(box + m_eff^2) phi = 0",
        "Klein-Gordon-class",
        "Non-claim boundary",
    ]
    for marker in required_strings:
        assert marker in text, f"Scalar field derivation report missing marker: {marker}"


def test_toe_qft_scalar_field_equation_artifact_schema_is_pinned() -> None:
    artifact = _read_json(ARTIFACT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_scalar_field_equations_v0"
    assert artifact.get("phase") == "PHASE_1_CLASSICAL_SCALAR_FIELD"
    assert artifact.get("source") == "master_action_scalar_slice"

    assumptions = artifact.get("assumptions", [])
    assert isinstance(assumptions, list)
    assert "real_scalar_field_phi" in assumptions
    assert "vanishing_boundary_variation_terms" in assumptions

    eom = artifact.get("euler_lagrange", {})
    assert eom.get("general_form") == "d_mu(dL/d(d_mu phi)) - dL/dphi = 0"
    assert eom.get("equation_of_motion") == "box(phi) + m_eff^2 * phi + dV_int/dphi = 0"

    kg = artifact.get("klein_gordon_mapping", {})
    assert kg.get("condition") == "dV_int/dphi = 0"
    assert kg.get("equation") == "(box + m_eff^2) phi = 0"
    assert kg.get("classification") == "KLEIN_GORDON_CLASS_COMPATIBLE"

    assert artifact.get("status") == "PINNED_PHASE1_KG_CLASS_ROUTE"
