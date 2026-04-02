from __future__ import annotations

import json
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
ARCHITECTURE_SCHEMA_PATH = REPO_ROOT / "ARCHITECTURE_SCHEMA_v1.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_governance_surface_inventory_declares_existing_files_and_patterns() -> None:
    schema = _read_json(ARCHITECTURE_SCHEMA_PATH)
    inventory = schema.get("governance_surface_inventory")
    assert isinstance(inventory, dict), "Missing governance_surface_inventory in architecture schema."

    governance_docs = inventory.get("governance_docs")
    assert isinstance(governance_docs, dict), "Missing governance_docs inventory declaration."

    fixed_files = governance_docs.get("fixed_files")
    assert isinstance(fixed_files, list) and fixed_files, "governance_docs.fixed_files must be a non-empty list."
    for rel_path in fixed_files:
        assert isinstance(rel_path, str) and rel_path, "Each fixed_files entry must be a non-empty string."
        target = REPO_ROOT / rel_path
        assert target.exists(), f"Schema inventory fixed file does not exist: {rel_path}"

    glob_patterns = governance_docs.get("glob_patterns")
    assert isinstance(glob_patterns, list) and glob_patterns, "governance_docs.glob_patterns must be a non-empty list."
    for pattern in glob_patterns:
        assert isinstance(pattern, str) and pattern, "Each glob_patterns entry must be a non-empty string."
        matches = list(REPO_ROOT.glob(pattern))
        assert matches, f"Schema inventory glob pattern produced no matches: {pattern}"
