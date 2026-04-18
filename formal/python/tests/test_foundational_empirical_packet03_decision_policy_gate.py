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
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET03_MATRIX_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_packet03_decision_policy_gate() -> None:
    matrix = _read_json(MATRIX_PATH)
    rows = matrix.get("rows", {})
    assert isinstance(rows, dict) and rows

    decisions = []
    for lane, row in rows.items():
        artifact = _read_json(REPO_ROOT / row["artifact_path"])
        payload = artifact.get("payload", {})
        decision = payload.get("decision")
        assert decision in {"RETAIN_v0", "PRUNE_v0", "INCONCLUSIVE_v0"}, (
            f"{lane}: unexpected packet-03 decision `{decision}`."
        )
        decisions.append(decision)

    assert set(decisions) == {"INCONCLUSIVE_v0"}, (
        "Packet-03 baseline policy requires INCONCLUSIVE_v0 across pillars until packet-04 or higher."
    )
