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
REPORT_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "toe_qft_scalar_normalization_report_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_scalar_one_particle_state_artifact_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_toe_qft_scalar_normalization_report_has_required_structure() -> None:
    text = _read(REPORT_PATH)
    required_strings = [
        "Normalization hardening",
        "[a_k, a_q^dagger] = (2pi)^3 delta^3(k-q)",
        "Vacuum and one-particle-state construction (bounded)",
        "a_k |0> = 0",
        "|k> = a_k^dagger |0>",
        "<k|q> = (2pi)^3 delta^3(k-q)",
        "Non-claim boundary:",
        "does not claim multi-particle scattering completion",
    ]
    for marker in required_strings:
        assert marker in text, f"Normalization report missing marker: {marker}"


def test_toe_qft_scalar_one_particle_state_artifact_schema_is_pinned() -> None:
    artifact = _read_json(ARTIFACT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_scalar_one_particle_state_artifact_v0"
    assert artifact.get("phase") == "PHASE_3_ROUTE_A_NORMALIZATION_ONE_PARTICLE_HARDENING"
    assert artifact.get("source") == "free_scalar_normalization_route"

    normalization = artifact.get("normalization", {})
    assert normalization.get("ladder_commutator") == "[a_k,a_q_dagger]=(2pi)^3 delta^3(k-q)"
    assert normalization.get("vacuum_condition") == "a_k|0>=0"
    assert normalization.get("one_particle_definition") == "|k>=a_k^dagger|0>"
    assert normalization.get("inner_product") == "<k|q>=(2pi)^3 delta^3(k-q)"

    hamiltonian = artifact.get("hamiltonian_interpretation", {})
    assert hamiltonian.get("occupation_density_operator") == "a_k^dagger a_k"
    assert hamiltonian.get("bounded_free_scalar") is True

    assumptions = artifact.get("assumptions", [])
    assert "free_scalar_regime_only" in assumptions
    assert "distribution_smearing_inherited_from_tranches_e_f" in assumptions

    assert artifact.get("status") == "PINNED_ROUTE_A_NORMALIZATION_ONE_PARTICLE_HARDENING"
