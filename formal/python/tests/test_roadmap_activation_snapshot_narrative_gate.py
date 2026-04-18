from __future__ import annotations

import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _activation_snapshot_block(text: str) -> str:
    start = text.find("Activation Snapshot (historical)")
    assert start >= 0, "Roadmap must contain `Activation Snapshot (historical)` narrative marker."

    tail = text[start:]
    stop_marker = "- Path 2 closure sprint lock"
    stop = tail.find(stop_marker)
    assert stop >= 0, f"Roadmap activation snapshot block must be bounded by `{stop_marker}`."
    return tail[:stop]


def test_activation_snapshot_is_descriptive_only_and_non_authoritative() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    block = _activation_snapshot_block(roadmap_text)
    block_lower = block.lower()

    assert "descriptive only" in block_lower, "Activation snapshot block must declare descriptive-only status."

    has_adjudication_token = re.search(r"\b[A-Z0-9_]+_ADJUDICATION\s*:", block) is not None
    assert not has_adjudication_token, "Activation snapshot narrative block must not define adjudication tokens."
