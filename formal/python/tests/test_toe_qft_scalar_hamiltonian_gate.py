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
REPORT_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "toe_qft_scalar_canonical_momentum_report_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_scalar_hamiltonian_density_artifact_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_toe_qft_scalar_canonical_momentum_report_has_required_structure() -> None:
    text = _read(REPORT_PATH)
    required_strings = [
        "Canonical momentum definition",
        "pi(x) = dL_scalar / d(partial_t phi) = partial_t phi",
        "Hamiltonian density refinement",
        "H = 1/2 pi^2 + 1/2 |grad phi|^2 + 1/2 m_eff^2 phi^2 + V_int(phi)",
        "Operator-facing bounded interpretation",
        "Non-claim boundary:",
    ]
    for marker in required_strings:
        assert marker in text, f"Canonical momentum report missing marker: {marker}"


def test_toe_qft_scalar_hamiltonian_density_artifact_schema_is_pinned() -> None:
    artifact = _read_json(ARTIFACT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_scalar_hamiltonian_density_artifact_v0"
    assert artifact.get("phase") == "PHASE_3_ROUTE_A_QUANTIZATION_REFINEMENT"
    assert artifact.get("source") == "master_action_scalar_slice"

    momentum = artifact.get("canonical_momentum", {})
    assert momentum.get("definition") == "pi = dL/d(partial_t phi)"
    assert momentum.get("result") == "pi = partial_t(phi)"

    hamiltonian = artifact.get("hamiltonian_density", {})
    assert hamiltonian.get("legendre_relation") == "H = pi partial_t(phi) - L_scalar"
    assert hamiltonian.get("expanded_form") == "H = 1/2 pi^2 + 1/2 |grad phi|^2 + 1/2 m_eff^2 phi^2 + V_int(phi)"

    route = artifact.get("operator_facing_route", {})
    assert route.get("equal_time_commutator_phi_pi") == "[phi(t,x), pi(t,y)] = i delta^3(x-y)"
    assert route.get("equal_time_commutator_phi_phi") == "[phi,phi] = 0"
    assert route.get("equal_time_commutator_pi_pi") == "[pi,pi] = 0"

    assumptions = artifact.get("assumptions", [])
    assert "equal_time_foliation_admissible" in assumptions
    assert "operator_valued_distribution_pairing" in assumptions

    assert artifact.get("status") == "PINNED_ROUTE_A_CANONICAL_MOMENTUM_HAMILTONIAN_REFINEMENT"
