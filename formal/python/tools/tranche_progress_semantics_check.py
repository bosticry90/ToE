from __future__ import annotations

import argparse
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
STANDARD_PATH = REPO_ROOT / "formal" / "docs" / "release" / "UNIFIED_TRANCHE_STANDARD_v0.md"

REQUIRED_TERMS = [
    "target_blocker_state_change",
    "actual_blocker_state_change",
    "progress_classification",
    "PROGRESS",
    "MAINTENANCE",
    "REWORK_ROUTED",
]


def _read(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Validate tranche progress semantics in unified tranche standard.")
    parser.add_argument("--path", type=Path, default=STANDARD_PATH, help="Path to unified tranche standard markdown.")
    args = parser.parse_args(argv)

    path = args.path if args.path.is_absolute() else (REPO_ROOT / args.path)
    text = _read(path)

    missing = [term for term in REQUIRED_TERMS if term not in text]
    if missing:
        raise AssertionError(f"Unified tranche standard missing required progress-semantics terms: {', '.join(missing)}")

    print("tranche_progress_semantics_check: ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
