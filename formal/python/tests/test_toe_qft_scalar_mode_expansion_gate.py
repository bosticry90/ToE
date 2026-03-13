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
REPORT_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "toe_qft_scalar_mode_expansion_report_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_scalar_creation_annihilation_artifact_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_toe_qft_scalar_mode_expansion_report_has_required_structure() -> None:
    text = _read(REPORT_PATH)
    required_strings = [
        "Mode expansion hardening",
        "phi(t,x) = integral d^3k",
        "Creation/annihilation operator interpretation",
        "[a_k, a_q^dagger] = (2pi)^3 delta^3(k-q)",
        "Equal-time commutator compatibility (bounded)",
        "Non-claim boundary:",
        "does not claim interacting-field renormalization completion",
    ]
    for marker in required_strings:
        assert marker in text, f"Mode expansion report missing marker: {marker}"


def test_toe_qft_scalar_creation_annihilation_artifact_schema_is_pinned() -> None:
    artifact = _read_json(ARTIFACT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_scalar_creation_annihilation_artifact_v0"
    assert artifact.get("phase") == "PHASE_3_ROUTE_A_MODE_EXPANSION_OPERATOR_HARDENING"
    assert artifact.get("source") == "free_scalar_mode_expansion_route"

    mode = artifact.get("mode_expansion", {})
    assert "phi(t,x)=int[d^3k" in mode.get("field_expression", "")
    assert mode.get("omega_k") == "sqrt(k^2 + m^2)"

    commutators = artifact.get("ladder_commutators", {})
    assert commutators.get("[a_k,a_q_dagger]") == "(2pi)^3 delta^3(k-q)"
    assert commutators.get("[a_k,a_q]") == "0"
    assert commutators.get("[a_k_dagger,a_q_dagger]") == "0"

    interpretation = artifact.get("operator_interpretation", {})
    assert interpretation.get("a_k_role") == "occupation_lowering"
    assert interpretation.get("a_k_dagger_role") == "occupation_raising"
    assert interpretation.get("fock_posture_bounded") is True

    assumptions = artifact.get("assumptions", [])
    assert "free_scalar_regime_only" in assumptions
    assert "distribution_smearing_inherited_from_tranche_e" in assumptions

    assert artifact.get("status") == "PINNED_ROUTE_A_MODE_EXPANSION_OPERATOR_HARDENING"
