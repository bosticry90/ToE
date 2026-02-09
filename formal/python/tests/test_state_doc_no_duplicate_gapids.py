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
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"


def test_state_doc_has_no_duplicate_gapids() -> None:
    text = STATE_PATH.read_text(encoding="utf-8")
    gap_ids = re.findall(r"^GapID:\s*(\S+)\s*$", text, flags=re.MULTILINE)
    counts = Counter(gap_ids)
    duplicates = {gap_id: count for gap_id, count in counts.items() if count > 1}

    assert not duplicates, (
        "Duplicate GapID entries found in State_of_the_Theory.md: "
        + ", ".join(f"{gap_id} (x{count})" for gap_id, count in sorted(duplicates.items()))
    )
