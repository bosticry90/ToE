from __future__ import annotations

import re
from collections import Counter
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
EXPECTED_PILLAR_SET = {
    "PILLAR-GR",
    "PILLAR-QM",
    "PILLAR-EM",
    "PILLAR-SR",
    "PILLAR-QFT",
    "PILLAR-STAT",
    "PILLAR-COSMO",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _pillar_rows(roadmap_text: str) -> list[str]:
    rows: list[str] = []
    for line in roadmap_text.splitlines():
        stripped = line.strip()
        m = re.match(r"^\|\s*`(PILLAR-[A-Z0-9]+)`\s*\|", stripped)
        if m:
            rows.append(m.group(1))
    return rows


def test_physics_roadmap_has_unique_pillar_rows() -> None:
    text = _read(ROADMAP_PATH)
    rows = _pillar_rows(text)
    assert rows, "No pillar rows found in PHYSICS_ROADMAP_v0.md."
    counts = Counter(rows)
    duplicates = sorted(pillar for pillar, count in counts.items() if count > 1)
    assert not duplicates, (
        "PHYSICS_ROADMAP_v0.md has duplicate pillar row(s): "
        + ", ".join(f"{pillar} (x{counts[pillar]})" for pillar in duplicates)
    )


def test_physics_roadmap_has_expected_pillar_set() -> None:
    text = _read(ROADMAP_PATH)
    actual_set = set(_pillar_rows(text))
    missing = sorted(EXPECTED_PILLAR_SET - actual_set)
    unexpected = sorted(actual_set - EXPECTED_PILLAR_SET)
    assert not missing and not unexpected, (
        "PHYSICS_ROADMAP_v0.md pillar set drift detected. "
        f"missing={missing} unexpected={unexpected}"
    )
