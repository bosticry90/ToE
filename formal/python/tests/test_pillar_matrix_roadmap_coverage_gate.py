from __future__ import annotations

import json
import re
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"

ROADMAP_PILLAR_ROW = re.compile(r"(?m)^\|\s*`(PILLAR-[A-Z0-9-]+)`\s*\|(.*)$")


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _roadmap_pillars_from_table(active_text: str) -> list[str]:
    rows = ROADMAP_PILLAR_ROW.findall(active_text)
    pillars: list[str] = []
    for pillar_id, row_tail in rows:
        if "FULL-DERIVATION-DISCHARGE" in row_tail:
            pillars.append(pillar_id)
    return pillars


def test_roadmap_pillars_are_matrix_registered() -> None:
    matrix = _read_json(MATRIX_PATH)
    matrix_pillars = set(matrix.get("pillars", {}).keys())
    assert matrix_pillars, "PILLAR_STATUS_MATRIX_v1.json must define at least one pillar row."

    roadmap_active, _ = split_active_and_archived(_read(ROADMAP_PATH), ROADMAP_PATH)
    roadmap_rows = _roadmap_pillars_from_table(roadmap_active)
    assert roadmap_rows, (
        "PHYSICS_ROADMAP_v0.md must contain at least one pillar row with a standardized FULL-DERIVATION-DISCHARGE target."
    )

    duplicates = sorted({pillar for pillar in roadmap_rows if roadmap_rows.count(pillar) > 1})
    assert not duplicates, "Duplicate pillar rows found in roadmap table: " + ", ".join(duplicates)

    roadmap_pillars = set(roadmap_rows)
    missing_in_matrix = sorted(roadmap_pillars - matrix_pillars)
    assert not missing_in_matrix, (
        "Roadmap pillars missing in matrix: " + ", ".join(missing_in_matrix) +
        ". Add rows to formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json."
    )
