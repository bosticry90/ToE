from __future__ import annotations

import subprocess
import unicodedata
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))

# Existing authority-bound historical paths are preserved. These ceilings stop
# additional portability debt without forcing unsafe evidence renames.
MAX_TRACKED_PATH_LENGTH = 273
MAX_PATHS_AT_LEAST_240 = 31
MAX_PATHS_OVER_260 = 10


def _tracked_paths() -> list[str]:
    completed = subprocess.run(
        ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard"],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
    )
    return [
        item.decode("utf-8", errors="strict")
        for item in completed.stdout.split(b"\0")
        if item
    ]


def test_tracked_paths_do_not_exceed_the_preserved_portability_budget() -> None:
    paths = _tracked_paths()
    lengths = [len(path) for path in paths]
    assert max(lengths) <= MAX_TRACKED_PATH_LENGTH
    assert sum(length >= 240 for length in lengths) <= MAX_PATHS_AT_LEAST_240
    assert sum(length > 260 for length in lengths) <= MAX_PATHS_OVER_260


def test_tracked_paths_have_no_case_or_unicode_normalization_collisions() -> None:
    paths = _tracked_paths()
    casefolded: dict[str, str] = {}
    normalized: dict[str, str] = {}
    for path in paths:
        folded = path.casefold()
        assert folded not in casefolded, f"case-insensitive path collision: {casefolded.get(folded)} / {path}"
        casefolded[folded] = path

        nfc = unicodedata.normalize("NFC", path)
        assert nfc not in normalized, f"Unicode-normalization path collision: {normalized.get(nfc)} / {path}"
        normalized[nfc] = path
