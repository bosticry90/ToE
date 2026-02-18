from __future__ import annotations

import json
import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _latest_lock_path() -> Path:
    versioned: list[tuple[int, Path]] = []
    for path in REPO_ROOT.glob("GOVERNANCE_VERSION_v*.lock"):
        m = re.fullmatch(r"GOVERNANCE_VERSION_v(\d+)\.lock", path.name)
        if m is None:
            continue
        versioned.append((int(m.group(1)), path))
    assert versioned, "Missing governance lock file (expected GOVERNANCE_VERSION_v*.lock)."
    versioned.sort()
    return versioned[-1][1]


def _loads_rejecting_duplicate_keys(text: str) -> dict:
    def _reject_duplicate_pairs(pairs: list[tuple[str, object]]) -> dict:
        obj: dict[str, object] = {}
        duplicates: list[str] = []
        for key, value in pairs:
            if key in obj:
                duplicates.append(key)
            obj[key] = value
        if duplicates:
            unique_dupes = ", ".join(sorted(set(duplicates)))
            raise ValueError(f"Duplicate JSON key(s): {unique_dupes}")
        return obj

    parsed = json.loads(text, object_pairs_hook=_reject_duplicate_pairs)
    assert isinstance(parsed, dict), "Governance lock JSON must be an object."
    return parsed


def test_governance_lock_rejects_duplicate_json_keys() -> None:
    lock_path = _latest_lock_path()
    lock_text = _read(lock_path)
    try:
        _loads_rejecting_duplicate_keys(lock_text)
    except ValueError as exc:
        raise AssertionError(
            f"{lock_path.name} contains duplicate JSON keys and is not governance-safe: {exc}"
        ) from exc
