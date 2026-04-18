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
REPORT_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "toe_qft_scalar_canonical_quantization_report_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_scalar_canonical_quantization_artifact_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_toe_qft_scalar_canonical_quantization_report_has_required_structure() -> None:
    text = _read(REPORT_PATH)
    required_strings = [
        "Route A ingredients",
        "Canonical momentum",
        "Hamiltonian density",
        "Equal-time canonical commutation structure",
        "[phi(t,x), pi(t,y)] = i delta^3(x-y)",
        "Non-claim boundary:",
        "does not claim interacting renormalization completion",
    ]
    for marker in required_strings:
        assert marker in text, f"Quantization report missing marker: {marker}"


def test_toe_qft_scalar_canonical_quantization_artifact_schema_is_pinned() -> None:
    artifact = _read_json(ARTIFACT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_scalar_canonical_quantization_artifact_v0"
    assert artifact.get("phase") == "PHASE_3_ROUTE_A_CANONICAL_QUANTIZATION"
    assert artifact.get("source") == "master_action_scalar_slice"

    canonical_variables = artifact.get("canonical_variables", {})
    assert canonical_variables.get("field") == "phi"
    assert canonical_variables.get("canonical_momentum") == "pi = partial_t(phi)"

    assert artifact.get("hamiltonian_density") == (
        "H = 1/2 pi^2 + 1/2 |grad phi|^2 + 1/2 m_eff^2 phi^2 + V_int(phi)"
    )

    commutators = artifact.get("equal_time_commutators", {})
    assert commutators.get("[phi,pi]") == "i delta^3(x-y)"
    assert commutators.get("[phi,phi]") == "0"
    assert commutators.get("[pi,pi]") == "0"

    assumptions = artifact.get("assumptions", [])
    assert "equal_time_hypersurface_split" in assumptions
    assert "operator_valued_distribution_framework" in assumptions

    assert artifact.get("route_status") == "BOUNDED_CANONICAL_QUANTIZATION_ROUTE_DECLARED"
    assert artifact.get("status") == "PINNED_PHASE3_CANONICAL_QUANTIZATION_KICKOFF"
