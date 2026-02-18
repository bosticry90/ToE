from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Iterable


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
EXCLUDED_NON_AUTHORITATIVE_DIRS = {
    ".git",
    ".lake",
    ".venv",
    "__pycache__",
    "archive",
    "backup",
    "scratch",
    "tests_quarantine",
}


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


def _authoritative_json_surfaces() -> list[Path]:
    def _is_authoritative_surface(path: Path) -> bool:
        rel = path.relative_to(REPO_ROOT)
        for part in rel.parts[:-1]:
            if part.startswith(".") or part in EXCLUDED_NON_AUTHORITATIVE_DIRS:
                return False
        return True

    paths: set[Path] = set()

    paths.add(_latest_lock_path())
    paths.update(
        path
        for path in REPO_ROOT.rglob("*.lock")
        if path.is_file() and _is_authoritative_surface(path)
    )
    paths.update(
        path
        for path in REPO_ROOT.glob("ARCHITECTURE_SCHEMA_v*.json")
        if path.is_file() and _is_authoritative_surface(path)
    )
    paths.update(
        path
        for path in REPO_ROOT.rglob("*_pinned_*.json")
        if path.is_file() and _is_authoritative_surface(path)
    )

    return sorted(paths)


def _loads_rejecting_duplicate_keys(text: str, *, source: Path) -> dict:
    def _reject_duplicate_pairs(pairs: list[tuple[str, object]]) -> dict:
        obj: dict[str, object] = {}
        duplicates: list[str] = []
        for key, value in pairs:
            if key in obj:
                duplicates.append(key)
            obj[key] = value
        if duplicates:
            unique_dupes = ", ".join(sorted(set(duplicates)))
            raise ValueError(f"{source}: duplicate JSON key(s): {unique_dupes}")
        return obj

    try:
        parsed = json.loads(text, object_pairs_hook=_reject_duplicate_pairs)
    except json.JSONDecodeError as exc:
        raise ValueError(
            f"{source}: invalid JSON content ({exc.msg} at line {exc.lineno}, column {exc.colno})"
        ) from exc

    assert isinstance(parsed, dict), "Governance lock JSON must be an object."
    return parsed


def _validate_no_duplicate_keys(paths: Iterable[Path]) -> list[str]:
    failures: list[str] = []
    for path in paths:
        try:
            _loads_rejecting_duplicate_keys(_read(path), source=path)
        except ValueError as exc:
            failures.append(str(exc))
    return failures


def test_authoritative_json_surfaces_reject_duplicate_keys() -> None:
    surfaces = _authoritative_json_surfaces()
    assert surfaces, "No authoritative JSON surfaces found for duplicate-key validation."

    failures = _validate_no_duplicate_keys(surfaces)
    assert not failures, (
        "Authoritative JSON surfaces must be valid JSON with unique keys:\n- "
        + "\n- ".join(failures)
    )
