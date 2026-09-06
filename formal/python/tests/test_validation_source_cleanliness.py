from __future__ import annotations

import subprocess
import sys
from pathlib import Path

from formal.python.tools import validation_source_cleanliness as guard


def _git(repo: Path, *args: str) -> None:
    subprocess.run(["git", *args], cwd=repo, check=True, capture_output=True)


def _fixture_repo(tmp_path: Path) -> Path:
    _git(tmp_path, "init")
    _git(tmp_path, "config", "user.name", "Cleanliness Test")
    _git(tmp_path, "config", "user.email", "cleanliness@example.invalid")
    source = tmp_path / "tracked.txt"
    source.write_text("before\n", encoding="utf-8", newline="\n")
    _git(tmp_path, "add", "tracked.txt")
    _git(tmp_path, "commit", "-m", "fixture")
    return source


def test_guard_passes_nonmutating_validation(tmp_path: Path) -> None:
    _fixture_repo(tmp_path)
    result = guard.run_guarded(
        [sys.executable, "-c", "print('read only')"],
        repo_root=tmp_path,
        require_clean_start=True,
    )
    assert result == 0


def test_guard_fails_when_validation_mutates_tracked_source(tmp_path: Path) -> None:
    source = _fixture_repo(tmp_path)
    result = guard.run_guarded(
        [
            sys.executable,
            "-c",
            f"from pathlib import Path; Path({str(source)!r}).write_text('after\\n')",
        ],
        repo_root=tmp_path,
        require_clean_start=True,
    )
    assert result == guard.MUTATION_EXIT


def test_guard_detects_mutation_even_when_source_was_already_dirty(tmp_path: Path) -> None:
    source = _fixture_repo(tmp_path)
    source.write_text("dirty-before\n", encoding="utf-8", newline="\n")
    result = guard.run_guarded(
        [
            sys.executable,
            "-c",
            f"from pathlib import Path; Path({str(source)!r}).write_text('dirty-after\\n')",
        ],
        repo_root=tmp_path,
    )
    assert result == guard.MUTATION_EXIT
