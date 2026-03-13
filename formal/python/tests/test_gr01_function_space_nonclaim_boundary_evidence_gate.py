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
NOTE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_FUNCTION_SPACE_NONCLAIM_BOUNDARY_EVIDENCE_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "gr01_function_space_nonclaim_boundary_evidence_v0.json"
ANALYTIC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_ANALYTIC_DISCHARGE_v0.md"
CANONICAL_EQ_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_CANONICAL_EQUIVALENCE_THEOREM_v0.md"
CRITERIA_PATH = REPO_ROOT / "formal" / "output" / "gr01_function_space_completion_criteria_cycle10_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_gr01_function_space_row03_nonclaim_boundary_has_concrete_evidence() -> None:
    note_text = _read(NOTE_PATH)
    analytic_text = _read(ANALYTIC_PATH)
    canonical_text = _read(CANONICAL_EQ_PATH)
    artifact = json.loads(_read(ARTIFACT_PATH))
    criteria = json.loads(_read(CRITERIA_PATH))

    for token in (
        "GR01_FUNCTION_SPACE_NONCLAIM_BOUNDARY_STATUS_v0: DISCHARGED_v0_CONCRETE_EVIDENCE_NONCLAIM",
        "GR01_FUNCTION_SPACE_NONCLAIM_BOUNDARY_SOBELOV_v0: NOT_CLAIMED",
        "GR01_FUNCTION_SPACE_NONCLAIM_BOUNDARY_UNIQUENESS_v0: NOT_CLAIMED",
        "GR01_FUNCTION_SPACE_NONCLAIM_BOUNDARY_CONTINUUM_COMPLETION_v0: NOT_CLAIMED",
    ):
        assert token in note_text

    assert "no continuum Sobolev-class claim is made" in analytic_text
    assert "no uniqueness/Sobolev-class PDE theorem is claimed" in canonical_text

    assert artifact["artifact_id"] == "gr01_function_space_nonclaim_boundary_evidence_v0"
    assert artifact["status"] == "DISCHARGED_v0_CONCRETE_EVIDENCE_NONCLAIM"
    assert artifact["boundary_tokens"]["sobolev"] == "NOT_CLAIMED"
    assert artifact["boundary_tokens"]["uniqueness"] == "NOT_CLAIMED"

    row_map = {row["row_id"]: row for row in criteria["criteria_rows"]}
    row3 = row_map["GR01_FUNCTION_SPACE_CRITERIA_ROW_03_v0"]
    assert row3["status"] == "DISCHARGED_v0_CONCRETE_EVIDENCE_NONCLAIM"
    assert "formal/docs/paper/TOE_GR01_FUNCTION_SPACE_NONCLAIM_BOUNDARY_EVIDENCE_v0.md" in row3["evidence_tokens"]
    assert "formal/output/gr01_function_space_nonclaim_boundary_evidence_v0.json" in row3["evidence_tokens"]

    for text in (_read(STATE_PATH), _read(ROADMAP_PATH)):
        assert "formal/docs/paper/TOE_GR01_FUNCTION_SPACE_NONCLAIM_BOUNDARY_EVIDENCE_v0.md" in text
        assert "formal/output/gr01_function_space_nonclaim_boundary_evidence_v0.json" in text
        assert "formal/python/tests/test_gr01_function_space_nonclaim_boundary_evidence_gate.py" in text