from __future__ import annotations

import argparse
import os
import subprocess
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
LEAN_PROJECT = REPO_ROOT / "formal" / "toe_formal"


def bounded_lake_command(
    *, jobs: int, targets: list[str], plan_only: bool = False
) -> list[str]:
    if jobs not in (1, 2):
        raise ValueError("This repository bounds exhaustive Lake scheduling to 1 or 2 jobs.")
    if not targets:
        raise ValueError("At least one Lake target is required.")

    command = ["lake", "--quiet", "--no-ansi"]
    if plan_only:
        command.append("--no-build")
    command.extend(["build", *targets])
    return command


def bounded_lake_environment(jobs: int) -> dict[str, str]:
    if jobs not in (1, 2):
        raise ValueError("This repository bounds exhaustive Lake scheduling to 1 or 2 jobs.")
    environment = os.environ.copy()
    environment["LEAN_NUM_THREADS"] = str(jobs)
    return environment


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Run Lake through Lean's bounded task scheduler. This build-control "
            "utility does not authorize scientific or theorem promotion."
        )
    )
    parser.add_argument("--jobs", type=int, choices=(1, 2), default=1)
    parser.add_argument("--target", action="append", dest="targets", required=True)
    parser.add_argument(
        "--plan-only",
        action="store_true",
        help="Resolve the Lake build graph without compiling stale targets.",
    )
    args = parser.parse_args()

    command = bounded_lake_command(
        jobs=args.jobs, targets=args.targets, plan_only=args.plan_only
    )
    print(
        f"lean_bounded_lake: LEAN_NUM_THREADS={args.jobs}",
        subprocess.list2cmdline(command),
    )
    completed = subprocess.run(
        command,
        cwd=LEAN_PROJECT,
        env=bounded_lake_environment(args.jobs),
        check=False,
    )
    return completed.returncode


if __name__ == "__main__":
    raise SystemExit(main())
