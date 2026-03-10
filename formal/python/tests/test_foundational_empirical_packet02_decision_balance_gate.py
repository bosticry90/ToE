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
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET02_MATRIX_v0.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_packet02_decision_balance_gate() -> None:
    matrix = _read_json(MATRIX_PATH)
    rows = matrix.get("rows", {})
    assert isinstance(rows, dict) and rows

    decisions = []
    for lane, row in rows.items():
        artifact = _read_json(REPO_ROOT / row["artifact_path"])
        payload = artifact.get("payload", {})
        decision = payload.get("decision")
        assert decision in {"RETAIN_v0", "PRUNE_v0", "INCONCLUSIVE_v0"}, (
            f"{lane}: unexpected packet-02 decision `{decision}`."
        )
        decisions.append(decision)

    decision_set = set(decisions)
    assert len(decision_set) >= 2, "Packet-02 decisions must not collapse to a single global value."
    assert any(d in {"RETAIN_v0", "PRUNE_v0"} for d in decisions), (
        "At least one packet-02 lane must be non-inconclusive to evidence decision-phase execution."
    )
    assert "RETAIN_v0" in decision_set, "Decision-phase balance requires at least one RETAIN_v0 lane."
    assert "PRUNE_v0" in decision_set, "Decision-phase balance requires at least one PRUNE_v0 lane."

    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    for ref in (
        "formal/python/tests/test_foundational_empirical_packet02_decision_balance_gate.py",
    ):
        assert ref in roadmap_text
        assert ref in state_text
