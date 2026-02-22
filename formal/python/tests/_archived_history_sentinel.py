from __future__ import annotations

from pathlib import Path


ARCHIVE_START_SENTINEL = "## ARCHIVED_HISTORY (NON-AUTHORITY)"
ARCHIVE_END_SENTINEL = "## END_ARCHIVED_HISTORY"


def split_active_and_archived(text: str, path: Path) -> tuple[str, str]:
    start_count = text.count(ARCHIVE_START_SENTINEL)
    end_count = text.count(ARCHIVE_END_SENTINEL)

    if start_count == 0 and end_count == 0:
        return text, ""

    assert start_count == 1, f"{path}: archived-history start sentinel must appear exactly once when present."
    assert end_count == 1, f"{path}: archived-history end sentinel must appear exactly once when present."

    start = text.find(ARCHIVE_START_SENTINEL)
    end = text.find(ARCHIVE_END_SENTINEL)
    assert start < end, f"{path}: archived-history sentinels must be ordered start -> end."

    archived_text = text[start + len(ARCHIVE_START_SENTINEL) : end]
    active_text = text[:start] + text[end + len(ARCHIVE_END_SENTINEL) :]
    return active_text, archived_text
