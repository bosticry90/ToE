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
DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_EMPIRICAL_COMPARISON_PACKET_04_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "em_empirical_comparison_packet_04_v0.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_em_empirical_comparison_packet_04_gate() -> None:
    text = _read(DOC_PATH)
    artifact = _read_json(ARTIFACT_PATH)
    payload = artifact.get("payload", {})
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)

    assert "EM_EMPIRICAL_PACKET_04_STATUS_v0: RUN_BOUNDED_v0_NONCLAIM" in text
    assert "EM_EMPIRICAL_PACKET_04_ARTIFACT_v0: em_empirical_comparison_packet_04_v0" in text
    assert "EM_EMPIRICAL_PACKET_04_DECISION_v0: INCONCLUSIVE_v0" in text
    assert payload.get("status") == "RUN_BOUNDED_v0_NONCLAIM"
    assert payload.get("decision") == "INCONCLUSIVE_v0"

    for ref in (
        "formal/docs/paper/DERIVATION_TARGET_EM_EMPIRICAL_COMPARISON_PACKET_04_v0.md",
        "formal/python/tests/test_em_empirical_comparison_packet_04_gate.py",
    ):
        assert ref in roadmap_text
        assert ref in state_text or ref in inventory_text
