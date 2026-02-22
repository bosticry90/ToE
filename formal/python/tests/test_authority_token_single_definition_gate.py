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
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _strip_archived_history(text: str) -> str:
    m = re.search(r"^##\s+Archived History\s*$", text, flags=re.MULTILINE)
    if m is None:
        return text
    return text[: m.start()]


def _count_token_definitions(text: str, token_name: str) -> int:
    return len(re.findall(rf"\b{re.escape(token_name)}\s*:", text))


def _token_values(text: str, token_name: str) -> list[str]:
    return re.findall(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)


def test_authority_token_definitions_are_single_in_active_mirrors_and_noncontradictory_in_canonical_docs() -> None:
    matrix = _read_json(MATRIX_PATH)
    pillars = matrix.get("pillars", {})
    assert pillars, "PILLAR_STATUS_MATRIX_v1.json must define at least one pillar row."

    state_text = _strip_archived_history(_read(STATE_PATH))
    roadmap_text = _strip_archived_history(_read(ROADMAP_PATH))

    for pillar_id, entry in sorted(pillars.items()):
        discharge_rel = entry.get("discharge_doc")
        full_token_name = entry.get("full_derivation_token")
        inevitability_token_name = entry.get("inevitability_token")

        assert isinstance(discharge_rel, str) and discharge_rel, f"{pillar_id}: missing discharge_doc in matrix row."
        assert isinstance(full_token_name, str) and full_token_name, f"{pillar_id}: missing full_derivation_token in matrix row."
        assert isinstance(inevitability_token_name, str) and inevitability_token_name, f"{pillar_id}: missing inevitability_token in matrix row."

        discharge_text = _strip_archived_history(_read(REPO_ROOT / discharge_rel))

        for token_name in (full_token_name, inevitability_token_name):
            state_count = _count_token_definitions(state_text, token_name)
            roadmap_count = _count_token_definitions(roadmap_text, token_name)

            assert state_count == 1, f"{pillar_id}: `{token_name}` must be defined exactly once in active state surface; found {state_count}."
            assert roadmap_count == 1, f"{pillar_id}: `{token_name}` must be defined exactly once in roadmap surface; found {roadmap_count}."

            canonical_values = _token_values(discharge_text, token_name)
            assert canonical_values, f"{pillar_id}: canonical discharge doc missing `{token_name}`."
            assert len(set(canonical_values)) == 1, (
                f"{pillar_id}: canonical discharge doc has contradictory duplicate values for `{token_name}`: {sorted(set(canonical_values))}."
            )
