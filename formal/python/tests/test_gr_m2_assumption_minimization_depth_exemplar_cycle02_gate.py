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
TARGET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_GR_M2_ASSUMPTION_MINIMIZATION_DEPTH_EXEMPLAR_CYCLE02_v0.md"
)
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "gr_m2_assumption_minimization_depth_exemplar_cycle02_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_gr_m2_assumption_minimization_depth_exemplar_cycle02_gate() -> None:
    target_text = _read(TARGET_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    artifact = _read_json(ARTIFACT_PATH)
    payload = artifact.get("payload", {})

    assert "GR_M2_ASSUMPTION_MINIMIZATION_DEPTH_EXEMPLAR_CYCLE02_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM" in target_text
    assert (
        "GR_M2_ASSUMPTION_MINIMIZATION_DEPTH_EXEMPLAR_CYCLE02_ARTIFACT_v0: "
        "gr_m2_assumption_minimization_depth_exemplar_cycle02_v0"
    ) in target_text
    assert (
        "GR_M2_ASSUMPTION_MINIMIZATION_DEPTH_EXEMPLAR_CYCLE02_GATE_v0: "
        "ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED"
    ) in target_text

    assert artifact.get("artifact_id") == "gr_m2_assumption_minimization_depth_exemplar_cycle02_v0"
    assert payload.get("status") == "RUN_BOUNDED_v0_NONCLAIM"
    assert payload.get("depth_cycle") == "cycle02"

    for text in (state_text, roadmap_text):
        assert "formal/docs/paper/DERIVATION_TARGET_GR_M2_ASSUMPTION_MINIMIZATION_DEPTH_EXEMPLAR_CYCLE02_v0.md" in text
        assert "formal/output/gr_m2_assumption_minimization_depth_exemplar_cycle02_v0.json" in text
        assert "formal/python/tests/test_gr_m2_assumption_minimization_depth_exemplar_cycle02_gate.py" in text