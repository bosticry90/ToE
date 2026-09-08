from __future__ import annotations

import argparse
import hashlib
import subprocess
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
MUTATION_EXIT = 97


def tracked_source_snapshot(repo_root: Path) -> dict[str, str | None]:
    listed = subprocess.run(
        ["git", "ls-files", "-z"],
        cwd=repo_root,
        check=True,
        capture_output=True,
    ).stdout.split(b"\0")
    snapshot: dict[str, str | None] = {}
    for raw_path in listed:
        if not raw_path:
            continue
        relative_path = raw_path.decode("utf-8", errors="surrogateescape")
        path = repo_root / relative_path
        snapshot[relative_path] = (
            hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None
        )
    return snapshot


def tracked_status(repo_root: Path) -> bytes:
    """Compatibility status probe retained for callers that only need Git state."""
    return subprocess.run(
        ["git", "status", "--porcelain=v1", "-z", "--untracked-files=no"],
        cwd=repo_root,
        check=True,
        capture_output=True,
    ).stdout


def run_guarded(
    command: list[str],
    *,
    repo_root: Path = REPO_ROOT,
    require_clean_start: bool = False,
) -> int:
    before_status = tracked_status(repo_root)
    if require_clean_start and before_status:
        print("validation_source_cleanliness: tracked source is dirty before validation")
        return MUTATION_EXIT
    before = tracked_source_snapshot(repo_root)

    completed = subprocess.run(command, cwd=repo_root, check=False)
    after = tracked_source_snapshot(repo_root)
    after_status = tracked_status(repo_root)
    if after != before or after_status != before_status:
        print("validation_source_cleanliness: tracked-source mutation detected")
        subprocess.run(
            ["git", "diff", "--no-ext-diff", "--stat", "HEAD"],
            cwd=repo_root,
            check=False,
        )
        return MUTATION_EXIT
    return completed.returncode


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Run a validation phase and fail if it changes tracked source."
    )
    parser.add_argument("--require-clean-start", action="store_true")
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        parser.error("a validation command is required after --")
    return run_guarded(command, require_clean_start=args.require_clean_start)


if __name__ == "__main__":
    raise SystemExit(main())
