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
NOTE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_FUNCTION_SPACE_CONTINUUM_REGULARITY_ROUTE_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "gr01_function_space_continuum_regularity_route_v0.json"
CRITERIA_PATH = REPO_ROOT / "formal" / "output" / "gr01_function_space_completion_criteria_cycle10_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_gr01_function_space_row02_route_is_explicitated() -> None:
    note_text = _read(NOTE_PATH)
    artifact = json.loads(_read(ARTIFACT_PATH))
    criteria = json.loads(_read(CRITERIA_PATH))

    for token in (
        "GR01_FUNCTION_SPACE_CONTINUUM_ROUTE_STATUS_v0: ROUTE_EXPLICITATED_v0_NONCLAIM",
        "GR01_FUNCTION_SPACE_CONTINUUM_ROUTE_TARGET_CLASS_v0: H1_LOCAL_TO_H2_WEAK_ROUTE_DECLARED",
        "GR01_FUNCTION_SPACE_CONTINUUM_ROUTE_MILESTONE_01_v0: DISCRETE_TO_CONTINUUM_CARRIER_MAP_PINNED",
        "GR01_FUNCTION_SPACE_CONTINUUM_ROUTE_MILESTONE_02_v0: WEAK_DERIVATIVE_WITNESS_TEMPLATE_PINNED",
        "GR01_FUNCTION_SPACE_CONTINUUM_ROUTE_MILESTONE_03_v0: BOUNDARY_TRACE_CONTRACT_PINNED",
        "GR01_FUNCTION_SPACE_CONTINUUM_ROUTE_MILESTONE_04_v0: SOBELOV_CLASS_ADMISSIBILITY_CHECKLIST_PINNED",
    ):
        assert token in note_text

    assert artifact["artifact_id"] == "gr01_function_space_continuum_regularity_route_v0"
    assert artifact["status"] == "ROUTE_EXPLICITATED_v0_NONCLAIM"
    assert artifact["target_class"] == "H1_LOCAL_TO_H2_WEAK_ROUTE_DECLARED"

    row_map = {row["row_id"]: row for row in criteria["criteria_rows"]}
    row2 = row_map["GR01_FUNCTION_SPACE_CRITERIA_ROW_02_v0"]
    assert row2["status"] == "ROUTE_EXPLICITATED_v0_NONCLAIM"
    assert "formal/docs/paper/TOE_GR01_FUNCTION_SPACE_CONTINUUM_REGULARITY_ROUTE_v0.md" in row2["evidence_tokens"]
    assert "formal/output/gr01_function_space_continuum_regularity_route_v0.json" in row2["evidence_tokens"]

    for text in (_read(STATE_PATH), _read(ROADMAP_PATH)):
        assert "formal/docs/paper/TOE_GR01_FUNCTION_SPACE_CONTINUUM_REGULARITY_ROUTE_v0.md" in text
        assert "formal/output/gr01_function_space_continuum_regularity_route_v0.json" in text
        assert "formal/python/tests/test_gr01_function_space_continuum_regularity_route_gate.py" in text