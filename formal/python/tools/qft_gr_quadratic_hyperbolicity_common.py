from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any, Callable

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
CAPTURED_AT_UTC = "2026-07-28T00:00:00Z"


class QuadraticHyperbolicityError(RuntimeError):
    pass


def canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(
            value,
            allow_nan=False,
            ensure_ascii=False,
            indent=2,
            sort_keys=True,
        )
        + "\n"
    ).encode("utf-8")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def read_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise QuadraticHyperbolicityError(f"expected JSON object: {path}")
    return value


def write_or_check(
    *,
    path: Path,
    build: Callable[[], dict[str, Any]],
    description: str,
) -> int:
    parser = argparse.ArgumentParser(description=description)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    expected = canonical_json_bytes(build())
    if args.write:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(expected)
        print(f"wrote {path.relative_to(REPO_ROOT).as_posix()}")
        return 0
    if not path.is_file() or path.read_bytes() != expected:
        print(f"stale or missing artifact: {path.relative_to(REPO_ROOT).as_posix()}")
        return 1
    print(f"{description}: OK")
    return 0
