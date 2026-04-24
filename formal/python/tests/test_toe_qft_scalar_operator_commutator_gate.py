from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
REPORT_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "toe_qft_scalar_operator_commutator_report_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_scalar_operator_commutator_artifact_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_toe_qft_scalar_operator_commutator_report_has_required_structure() -> None:
    text = _read(REPORT_PATH)
    required_strings = [
        "Equal-time commutator hardening",
        "[phi(t,x), pi(t,y)] = i delta^3(x-y)",
        "Operator-valued distribution framing",
        "Heisenberg-route consistency (bounded)",
        "Non-claim boundary:",
        "does not claim interacting-field commutator completion",
    ]
    for marker in required_strings:
        assert marker in text, f"Operator commutator report missing marker: {marker}"


def test_toe_qft_scalar_operator_commutator_artifact_schema_is_pinned() -> None:
    artifact = _read_json(ARTIFACT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_scalar_operator_commutator_artifact_v0"
    assert artifact.get("phase") == "PHASE_3_ROUTE_A_OPERATOR_COMMUTATOR_HARDENING"
    assert artifact.get("source") == "free_scalar_canonical_route"

    commutators = artifact.get("equal_time_commutators", {})
    assert commutators.get("[phi,pi]") == "i delta^3(x-y)"
    assert commutators.get("[phi,phi]") == "0"
    assert commutators.get("[pi,pi]") == "0"

    posture = artifact.get("operator_distribution_posture", {})
    assert posture.get("smearing_required") is True
    assert posture.get("pointwise_product_claimed") is False

    heisenberg = artifact.get("heisenberg_route_consistency", {})
    assert heisenberg.get("bounded_status") is True

    assumptions = artifact.get("assumptions", [])
    assert "free_scalar_regime_for_operator_hardening" in assumptions
    assert "equal_time_hypersurface_fixed" in assumptions

    assert artifact.get("status") == "PINNED_ROUTE_A_OPERATOR_COMMUTATOR_HARDENING"
