from __future__ import annotations

import re
from pathlib import Path

from formal.python.tests._archived_history_sentinel import (
    ARCHIVE_END_SENTINEL,
    ARCHIVE_START_SENTINEL,
    split_active_and_archived,
)
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SENTINEL_SURFACES = [
    REPO_ROOT / "State_of_the_Theory.md",
    REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md",
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_archived_history_sentinel_contract_integrity() -> None:
    for path in SENTINEL_SURFACES:
        text = _read(path)

        assert "## Archived History" not in text, f"{path}: legacy archived heading must be replaced by sentinel contract."

        assert text.count(ARCHIVE_START_SENTINEL) == 1, f"{path}: start sentinel must appear exactly once."
        assert text.count(ARCHIVE_END_SENTINEL) == 1, f"{path}: end sentinel must appear exactly once."

        start = text.find(ARCHIVE_START_SENTINEL)
        end = text.find(ARCHIVE_END_SENTINEL)
        assert start < end, f"{path}: start sentinel must precede end sentinel."

        active_text, archived_text = split_active_and_archived(text, path)
        assert archived_text.strip(), f"{path}: archived sentinel block must not be empty."

        end_to_eof = text[end + len(ARCHIVE_END_SENTINEL) :]
        assert ARCHIVE_START_SENTINEL not in end_to_eof, f"{path}: nested/duplicated archived start sentinel is forbidden."

        active_legacy = re.search(
            r"\bQFT_FULL_DERIVATION_(?:INEVITABILITY_)?ADJUDICATION\s*:\s*NOT_YET_",
            active_text,
        )
        assert active_legacy is None, (
            f"{path}: legacy QFT full-derivation NOT_YET adjudication token appears outside archived sentinel block."
        )
