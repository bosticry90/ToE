from __future__ import annotations

import json
import re
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SURFACE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_FUNCTION_SPACE_REGULARITY_SURFACE_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "gr01_function_space_completion_criteria_cycle10_v0.json"
ANALYTIC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_ANALYTIC_DISCHARGE_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_token_value(text: str, token_name: str) -> str:
    match = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-\.]+)", text)
    assert match is not None, f"Missing token `{token_name}`"
    return match.group(1)


def test_gr01_function_space_completion_criteria_are_pinned() -> None:
    surface_text = _read(SURFACE_PATH)
    analytic_text = _read(ANALYTIC_PATH)
    artifact = json.loads(_read(ARTIFACT_PATH))

    for token in (
        "GR01_FUNCTION_SPACE_COMPLETION_CRITERIA_v0: CYCLE10_ROW_LEVEL_CRITERIA_PINNED",
        "GR01_FUNCTION_SPACE_PARTIAL_DISCHARGE_STATUS_v0: ROW_01_AND_ROW_03_DISCHARGED_ROW_02_ROUTE_EXPLICITATED_NONCLAIM",
        "GR01_FUNCTION_SPACE_CRITERIA_ROW_01_v0: CURRENT_DISCRETE_REGULARITY_SCOPE_DISCHARGED_WITH_CONCRETE_EVIDENCE",
        "GR01_FUNCTION_SPACE_CRITERIA_ROW_02_v0: CONTINUUM_REGULARITY_CLASS_EXPLICITATION_ROUTE_EXPLICITATED_NONCLAIM",
        "GR01_FUNCTION_SPACE_CRITERIA_ROW_03_v0: SOBOLEV_AND_UNIQUENESS_NONCLAIM_BOUNDARY_DISCHARGED_WITH_CONCRETE_EVIDENCE",
        "GR01_FUNCTION_SPACE_CRITERIA_ROW_04_v0: STATE_ROADMAP_AND_GATE_SYNC_PINNED",
    ):
        assert token in surface_text

    assert "Function-Space / Regularity / Boundary Posture (v0)" in analytic_text
    assert artifact["artifact_id"] == "gr01_function_space_completion_criteria_cycle10_v0"
    assert artifact["status"] == "LOCKED_GR01_FUNCTION_SPACE_CRITERIA_CYCLE10_ROW01_ROW03_DISCHARGED_ROW02_ROUTE_NONCLAIM"
    assert len(artifact["criteria_rows"]) == 4

    row_map = {row["row_id"]: row for row in artifact["criteria_rows"]}
    assert row_map["GR01_FUNCTION_SPACE_CRITERIA_ROW_01_v0"]["status"] == "DISCHARGED_v0_CONCRETE_EVIDENCE_NONCLAIM"
    assert row_map["GR01_FUNCTION_SPACE_CRITERIA_ROW_02_v0"]["status"] == "ROUTE_EXPLICITATED_v0_NONCLAIM"
    assert row_map["GR01_FUNCTION_SPACE_CRITERIA_ROW_03_v0"]["status"] == "DISCHARGED_v0_CONCRETE_EVIDENCE_NONCLAIM"
    assert row_map["GR01_FUNCTION_SPACE_CRITERIA_ROW_04_v0"]["status"] == "PINNED"

    assert artifact["adjudication_posture"] == "ATTACK_TRACK_ACTIVE_NONCLAIM"
    assert (
        _extract_token_value(surface_text, "GR01_FUNCTION_SPACE_REGULARITY_STATUS_v0")
        == artifact["adjudication_posture"]
    )

    row02_surface = _extract_token_value(surface_text, "GR01_FUNCTION_SPACE_CRITERIA_ROW_02_v0")
    assert row02_surface == "CONTINUUM_REGULARITY_CLASS_EXPLICITATION_ROUTE_EXPLICITATED_NONCLAIM"
    assert any(
        token == "GR01_FUNCTION_SPACE_CONTINUUM_ROUTE_STATUS_v0: ROUTE_EXPLICITATED_v0_NONCLAIM"
        for token in row_map["GR01_FUNCTION_SPACE_CRITERIA_ROW_02_v0"]["evidence_tokens"]
    )

    row03_surface = _extract_token_value(surface_text, "GR01_FUNCTION_SPACE_CRITERIA_ROW_03_v0")
    assert row03_surface == "SOBOLEV_AND_UNIQUENESS_NONCLAIM_BOUNDARY_DISCHARGED_WITH_CONCRETE_EVIDENCE"
    assert any(
        token == "GR01_FUNCTION_SPACE_NONCLAIM_BOUNDARY_STATUS_v0: DISCHARGED_v0_CONCRETE_EVIDENCE_NONCLAIM"
        for token in row_map["GR01_FUNCTION_SPACE_CRITERIA_ROW_03_v0"]["evidence_tokens"]
    )

    for text in (_read(STATE_PATH), _read(ROADMAP_PATH)):
        assert "formal/output/gr01_function_space_completion_criteria_cycle10_v0.json" in text
        assert "formal/docs/paper/TOE_GR01_FUNCTION_SPACE_DISCRETE_REGULARITY_EVIDENCE_v0.md" in text
        assert "formal/output/gr01_function_space_discrete_regularity_evidence_v0.json" in text
        assert "formal/python/tests/test_gr01_function_space_discrete_regularity_evidence_gate.py" in text
        assert "formal/docs/paper/TOE_GR01_FUNCTION_SPACE_CONTINUUM_REGULARITY_ROUTE_v0.md" in text
        assert "formal/output/gr01_function_space_continuum_regularity_route_v0.json" in text
        assert "formal/python/tests/test_gr01_function_space_continuum_regularity_route_gate.py" in text
        assert "formal/docs/paper/TOE_GR01_FUNCTION_SPACE_NONCLAIM_BOUNDARY_EVIDENCE_v0.md" in text
        assert "formal/output/gr01_function_space_nonclaim_boundary_evidence_v0.json" in text
        assert "formal/python/tests/test_gr01_function_space_nonclaim_boundary_evidence_gate.py" in text
        assert "formal/python/tests/test_gr01_function_space_completion_criteria_gate.py" in text