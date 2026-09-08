from __future__ import annotations

import os
import subprocess
from pathlib import Path


TRACKED_OUTPUT_WRITE_ENV_VAR = "TOE_ALLOW_TRACKED_OUTPUT_WRITES"
TRACKED_OUTPUT_WRITE_ENV_VALUE = "1"


def _repo_relative(path: Path, repo_root: Path) -> Path:
    return path.resolve().relative_to(repo_root.resolve())


def _is_tracked_by_git(path: Path, repo_root: Path) -> bool:
    try:
        rel = _repo_relative(path, repo_root).as_posix()
    except ValueError:
        return False

    completed = subprocess.run(
        ["git", "ls-files", "--error-unmatch", "--", rel],
        cwd=str(repo_root),
        check=False,
        capture_output=True,
        text=True,
    )
    return completed.returncode == 0


def tracked_output_writes_allowed() -> bool:
    return os.environ.get(TRACKED_OUTPUT_WRITE_ENV_VAR) == TRACKED_OUTPUT_WRITE_ENV_VALUE


def assert_tracked_output_write_allowed(path: Path, *, repo_root: Path) -> None:
    """Fail closed before rewriting any tracked repository source artifact."""
    if not _is_tracked_by_git(path, repo_root):
        return

    if tracked_output_writes_allowed():
        return

    rel = _repo_relative(path, repo_root).as_posix()
    raise RuntimeError(
        "Refusing to write tracked canonical output or repository source without explicit "
        f"{TRACKED_OUTPUT_WRITE_ENV_VAR}={TRACKED_OUTPUT_WRITE_ENV_VALUE}: {rel}"
    )


def assert_tracked_output_writes_allowed(paths: list[Path], *, repo_root: Path) -> None:
    for path in paths:
        assert_tracked_output_write_allowed(path, repo_root=repo_root)
