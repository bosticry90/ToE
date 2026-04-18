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
TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_GR_CONTINUUM_LIMIT_BRIDGE_v0.md"
CRITERIA_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "gr_continuum_discharge_criteria_cycle10_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_gr_continuum_cycle10_criteria_rows_are_pinned() -> None:
    target_text = _read(TARGET_PATH)
    artifact = _read_json(CRITERIA_ARTIFACT_PATH)

    for token in (
        "GR_CONTINUUM_LIMIT_DISCHARGE_CRITERIA_v0: CYCLE10_ROW_LEVEL_CRITERIA_PINNED",
        "GR_CONTINUUM_LIMIT_CRITERIA_ROW_01_v0: REFINEMENT_TREND_MONOTONIC_PINNED",
        "GR_CONTINUUM_LIMIT_CRITERIA_ROW_02_v0: DISCRETE_TO_CONTINUUM_MAP_SURFACE_PINNED",
        "GR_CONTINUUM_LIMIT_CRITERIA_ROW_03_v0: BOUNDARY_ASSUMPTION_TRANSPARENCY_PINNED",
        "GR_CONTINUUM_LIMIT_CRITERIA_ROW_04_v0: STATE_GATE_SYNC_PINNED",
        "GR_CONTINUUM_LIMIT_DISCHARGE_CRITERIA_ARTIFACT_v0: gr_continuum_discharge_criteria_cycle10_v0",
    ):
        assert token in target_text

    assert artifact["artifact_id"] == "gr_continuum_discharge_criteria_cycle10_v0"
    assert artifact["status"] == "LOCKED_GR_CONTINUUM_CRITERIA_CYCLE10_PINNED"
    assert len(artifact["criteria_rows"]) == 4
    assert all(row["status"] == "PINNED" for row in artifact["criteria_rows"])

    row_map = {row["row_id"]: row for row in artifact["criteria_rows"]}
    assert "gr_continuum_refinement_trend_cycle1_v0" in row_map["GR_CONTINUUM_LIMIT_CRITERIA_ROW_01_v0"]["evidence_tokens"]
    assert "TARGET-GR-CONTINUUM-MICRO-01-REFINEMENT-TREND-v0" in row_map["GR_CONTINUUM_LIMIT_CRITERIA_ROW_02_v0"]["evidence_tokens"]
    assert "no infinite-domain uniqueness claim" in row_map["GR_CONTINUUM_LIMIT_CRITERIA_ROW_03_v0"]["evidence_tokens"]
    assert "State_of_the_Theory.md" in row_map["GR_CONTINUUM_LIMIT_CRITERIA_ROW_04_v0"]["evidence_tokens"]


def test_gr_continuum_cycle10_criteria_pointer_parity_in_state_and_roadmap() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    required_refs = (
        "formal/docs/paper/DERIVATION_TARGET_GR_CONTINUUM_LIMIT_BRIDGE_v0.md",
        "formal/output/gr_continuum_discharge_criteria_cycle10_v0.json",
        "formal/python/tests/test_gr_continuum_discharge_criteria_cycle10_gate.py",
    )

    for ref in required_refs:
        assert ref in state_text
        assert ref in roadmap_text