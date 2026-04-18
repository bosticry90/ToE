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
REPORT_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "toe_qft_scalar_propagator_report_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_scalar_two_point_function_artifact_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_toe_qft_scalar_propagator_report_has_required_structure() -> None:
    text = _read(REPORT_PATH)
    required_strings = [
        "Propagator and two-point hardening",
        "W(x-y) = <0| phi(x) phi(y) |0>",
        "Delta_F(x-y) = <0| T{phi(x) phi(y)} |0>",
        "Delta_F(k) = i / (k^2 - m^2 + i epsilon)",
        "(box + m^2) Delta_F(x-y) = -i delta^4(x-y)",
        "Non-claim boundary:",
        "does not claim renormalization completion",
    ]
    for marker in required_strings:
        assert marker in text, f"Propagator report missing marker: {marker}"


def test_toe_qft_scalar_two_point_artifact_schema_is_pinned() -> None:
    artifact = _read_json(ARTIFACT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_scalar_two_point_function_artifact_v0"
    assert artifact.get("phase") == "PHASE_3_ROUTE_A_PROPAGATOR_TWO_POINT_HARDENING"
    assert artifact.get("source") == "free_scalar_propagator_route"

    two_point = artifact.get("two_point_structure", {})
    assert two_point.get("wightman") == "W(x-y)=<0|phi(x)phi(y)|0>"
    assert two_point.get("time_ordered") == "Delta_F(x-y)=<0|T{phi(x)phi(y)}|0>"
    assert two_point.get("momentum_space") == "Delta_F(k)=i/(k^2-m^2+i*epsilon)"

    eom = artifact.get("eom_consistency", {})
    assert eom.get("operator_equation") == "(box+m^2)Delta_F(x-y)=-i delta^4(x-y)"
    assert eom.get("distribution_posture") is True

    route = artifact.get("route_compatibility", {})
    assert route.get("commutator_tranche_consistent") is True
    assert route.get("mode_expansion_tranche_consistent") is True
    assert route.get("normalization_tranche_consistent") is True

    assumptions = artifact.get("assumptions", [])
    assert "free_scalar_regime_only" in assumptions
    assert "distribution_smearing_required" in assumptions

    assert artifact.get("status") == "PINNED_ROUTE_A_PROPAGATOR_TWO_POINT_HARDENING"
