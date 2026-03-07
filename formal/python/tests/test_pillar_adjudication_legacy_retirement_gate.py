from __future__ import annotations

import json
import re
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


LEGACY_FORBIDDEN_PREFIXES = ("NOT_YET_",)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_matrix_defined_adjudication_tokens_do_not_reintroduce_legacy_not_yet_values() -> None:
    matrix = _read_json(MATRIX_PATH)
    pillars = matrix.get("pillars", {})
    assert pillars, "PILLAR_STATUS_MATRIX_v1.json must define at least one pillar row."

    state_text, _ = split_active_and_archived(_read(STATE_PATH), STATE_PATH)
    roadmap_text, _ = split_active_and_archived(_read(ROADMAP_PATH), ROADMAP_PATH)

    for pillar_id, entry in sorted(pillars.items()):
        discharge_rel = entry.get("discharge_doc")
        full_token_name = entry.get("full_derivation_token")
        inevitability_token_name = entry.get("inevitability_token")
        matrix_status = entry.get("matrix_status")

        assert isinstance(discharge_rel, str) and discharge_rel, f"{pillar_id}: missing discharge_doc in matrix row."
        assert isinstance(full_token_name, str) and full_token_name, f"{pillar_id}: missing full_derivation_token in matrix row."
        assert isinstance(inevitability_token_name, str) and inevitability_token_name, f"{pillar_id}: missing inevitability_token in matrix row."

        discharge_path = REPO_ROOT / discharge_rel
        discharge_text, _ = split_active_and_archived(_read(discharge_path), discharge_path)

        if matrix_status == "LOCKED":
            continue

        for token_name in (full_token_name, inevitability_token_name):
            for prefix in LEGACY_FORBIDDEN_PREFIXES:
                legacy_line = f"{token_name}: {prefix}"
                assert legacy_line not in state_text, f"{pillar_id}: legacy token present in active state surface: {legacy_line}..."
                assert legacy_line not in roadmap_text, f"{pillar_id}: legacy token present in roadmap surface: {legacy_line}..."
                assert legacy_line not in discharge_text, f"{pillar_id}: legacy token present in discharge surface: {legacy_line}..."
