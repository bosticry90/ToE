from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
STANDARD_PATH = REPO_ROOT / "formal" / "docs" / "release" / "GR01_PUBLICATION_THEOREM_CLAIM_ADVANCEMENT_STANDARD_v0.md"
CONTINUUM_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_GR_CONTINUUM_LIMIT_BRIDGE_v0.md"
FUNCTION_SPACE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_FUNCTION_SPACE_REGULARITY_SURFACE_v0.md"
FUNCTION_SPACE_ARTIFACT = REPO_ROOT / "formal" / "output" / "gr01_function_space_regularity_surface_v0.json"
FUNCTION_SPACE_CRITERIA_ARTIFACT = REPO_ROOT / "formal" / "output" / "gr01_function_space_completion_criteria_cycle10_v0.json"
FUNCTION_SPACE_EVIDENCE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_FUNCTION_SPACE_DISCRETE_REGULARITY_EVIDENCE_v0.md"
FUNCTION_SPACE_EVIDENCE_ARTIFACT = REPO_ROOT / "formal" / "output" / "gr01_function_space_discrete_regularity_evidence_v0.json"
FUNCTION_SPACE_ROUTE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_FUNCTION_SPACE_CONTINUUM_REGULARITY_ROUTE_v0.md"
FUNCTION_SPACE_ROUTE_ARTIFACT = REPO_ROOT / "formal" / "output" / "gr01_function_space_continuum_regularity_route_v0.json"
FUNCTION_SPACE_BOUNDARY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_FUNCTION_SPACE_NONCLAIM_BOUNDARY_EVIDENCE_v0.md"
FUNCTION_SPACE_BOUNDARY_ARTIFACT = REPO_ROOT / "formal" / "output" / "gr01_function_space_nonclaim_boundary_evidence_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_gr01_publication_theorem_claim_advancement_is_pinned() -> None:
    standard_text = _read(STANDARD_PATH)
    continuum_text = _read(CONTINUUM_PATH)
    function_text = _read(FUNCTION_SPACE_PATH)
    artifact = json.loads(FUNCTION_SPACE_ARTIFACT.read_text(encoding="utf-8"))
    criteria_artifact = json.loads(FUNCTION_SPACE_CRITERIA_ARTIFACT.read_text(encoding="utf-8"))
    evidence_text = _read(FUNCTION_SPACE_EVIDENCE_PATH)
    evidence_artifact = json.loads(FUNCTION_SPACE_EVIDENCE_ARTIFACT.read_text(encoding="utf-8"))
    route_text = _read(FUNCTION_SPACE_ROUTE_PATH)
    route_artifact = json.loads(FUNCTION_SPACE_ROUTE_ARTIFACT.read_text(encoding="utf-8"))
    boundary_text = _read(FUNCTION_SPACE_BOUNDARY_PATH)
    boundary_artifact = json.loads(FUNCTION_SPACE_BOUNDARY_ARTIFACT.read_text(encoding="utf-8"))

    for token in (
        "GR01_PUBLICATION_THEOREM_CLAIM_ADVANCEMENT_STANDARD_v0",
        "GR01_PUBLICATION_THEOREM_CLAIM_ADVANCEMENT_STATUS_v0: ATTACK_TRACK_ACTIVE_NONCLAIM",
        "GR01_PUBLICATION_THEOREM_CLAIM_CONTINUUM_TRACK_v0: DIRECT_ATTACK_REQUIRED",
        "GR01_PUBLICATION_THEOREM_CLAIM_FUNCTION_SPACE_TRACK_v0: DIRECT_ATTACK_REQUIRED",
        "GR01_PUBLICATION_THEOREM_CLAIM_COMPLETION_MODE_v0: CONTINUUM_AND_FUNCTION_SPACE_ROW_LEVEL_CRITERIA_PINNED",
        "GR01_PUBLICATION_THEOREM_CLAIM_CONTINUUM_CRITERIA_v0: CYCLE10_ROW_LEVEL_CRITERIA_PINNED",
        "GR01_PUBLICATION_THEOREM_CLAIM_FUNCTION_SPACE_CRITERIA_v0: CYCLE10_ROW_LEVEL_CRITERIA_PINNED",
    ):
        assert token in standard_text

    assert "GR_CONTINUUM_LIMIT_ADJUDICATION: DISCHARGED_v0_CONTINUUM_BRIDGE" in continuum_text
    assert "GR01_FUNCTION_SPACE_REGULARITY_STATUS_v0: ATTACK_TRACK_ACTIVE_NONCLAIM" in function_text
    assert "GR01_FUNCTION_SPACE_PARTIAL_DISCHARGE_STATUS_v0: ROW_01_AND_ROW_03_DISCHARGED_ROW_02_ROUTE_EXPLICITATED_NONCLAIM" in function_text
    assert "GR01_FUNCTION_SPACE_COMPLETION_CRITERIA_v0: CYCLE10_ROW_LEVEL_CRITERIA_PINNED" in function_text
    assert "GR01_FUNCTION_SPACE_DISCRETE_REGULARITY_STATUS_v0: DISCHARGED_v0_CONCRETE_EVIDENCE_NONCLAIM" in evidence_text
    assert "GR01_FUNCTION_SPACE_CONTINUUM_ROUTE_STATUS_v0: ROUTE_EXPLICITATED_v0_NONCLAIM" in route_text
    assert "GR01_FUNCTION_SPACE_NONCLAIM_BOUNDARY_STATUS_v0: DISCHARGED_v0_CONCRETE_EVIDENCE_NONCLAIM" in boundary_text
    assert artifact["status"] == "ATTACK_TRACK_ACTIVE_NONCLAIM"
    assert criteria_artifact["status"] == "LOCKED_GR01_FUNCTION_SPACE_CRITERIA_CYCLE10_ROW01_ROW03_DISCHARGED_ROW02_ROUTE_NONCLAIM"
    assert evidence_artifact["status"] == "DISCHARGED_v0_CONCRETE_EVIDENCE_NONCLAIM"
    assert route_artifact["status"] == "ROUTE_EXPLICITATED_v0_NONCLAIM"
    assert boundary_artifact["status"] == "DISCHARGED_v0_CONCRETE_EVIDENCE_NONCLAIM"

    for text in (_read(STATE_PATH), _read(ROADMAP_PATH)):
        assert "formal/docs/release/GR01_PUBLICATION_THEOREM_CLAIM_ADVANCEMENT_STANDARD_v0.md" in text
        assert "formal/docs/paper/TOE_GR01_FUNCTION_SPACE_REGULARITY_SURFACE_v0.md" in text
        assert "formal/docs/paper/TOE_GR01_FUNCTION_SPACE_DISCRETE_REGULARITY_EVIDENCE_v0.md" in text
        assert "formal/docs/paper/TOE_GR01_FUNCTION_SPACE_CONTINUUM_REGULARITY_ROUTE_v0.md" in text
        assert "formal/docs/paper/TOE_GR01_FUNCTION_SPACE_NONCLAIM_BOUNDARY_EVIDENCE_v0.md" in text
        assert "formal/output/gr01_function_space_completion_criteria_cycle10_v0.json" in text
        assert "formal/output/gr01_function_space_discrete_regularity_evidence_v0.json" in text
        assert "formal/output/gr01_function_space_continuum_regularity_route_v0.json" in text
        assert "formal/output/gr01_function_space_nonclaim_boundary_evidence_v0.json" in text
        assert "formal/python/tests/test_gr01_publication_theorem_claim_advancement_gate.py" in text
        assert "formal/python/tests/test_gr01_function_space_discrete_regularity_evidence_gate.py" in text
        assert "formal/python/tests/test_gr01_function_space_continuum_regularity_route_gate.py" in text
        assert "formal/python/tests/test_gr01_function_space_nonclaim_boundary_evidence_gate.py" in text
        assert "formal/python/tests/test_gr01_function_space_completion_criteria_gate.py" in text