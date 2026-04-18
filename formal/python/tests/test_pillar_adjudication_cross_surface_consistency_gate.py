from __future__ import annotations

import json
import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token_value(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def _extract_pillar_row(text: str, pillar_id: str) -> str:
    rows = [line.strip() for line in text.splitlines() if line.strip().startswith(f"| `{pillar_id}` |")]
    assert len(rows) == 1, f"Expected exactly one roadmap row for {pillar_id}, found {len(rows)}."
    return rows[0]


def test_matrix_driven_cross_surface_adjudication_consistency() -> None:
    matrix = _read_json(MATRIX_PATH)
    pillars = matrix.get("pillars", {})
    assert pillars, "PILLAR_STATUS_MATRIX_v1.json must define at least one pillar row."

    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    for pillar_id, entry in sorted(pillars.items()):
        discharge_rel = entry.get("discharge_doc")
        full_token_name = entry.get("full_derivation_token")
        inevitability_token_name = entry.get("inevitability_token")

        assert isinstance(discharge_rel, str) and discharge_rel, f"{pillar_id}: missing discharge_doc in matrix row."
        assert isinstance(full_token_name, str) and full_token_name, f"{pillar_id}: missing full_derivation_token in matrix row."
        assert isinstance(inevitability_token_name, str) and inevitability_token_name, f"{pillar_id}: missing inevitability_token in matrix row."

        discharge_text = _read(REPO_ROOT / discharge_rel)

        discharge_full = _extract_token_value(discharge_text, full_token_name)
        discharge_inevitability = _extract_token_value(discharge_text, inevitability_token_name)

        state_full = _extract_token_value(state_text, full_token_name)
        state_inevitability = _extract_token_value(state_text, inevitability_token_name)

        roadmap_full = _extract_token_value(roadmap_text, full_token_name)
        roadmap_inevitability = _extract_token_value(roadmap_text, inevitability_token_name)

        assert entry.get("full_derivation") == discharge_full == state_full == roadmap_full
        assert entry.get("inevitability") == discharge_inevitability == state_inevitability == roadmap_inevitability

        matrix_status = entry.get("matrix_status")
        assert isinstance(matrix_status, str) and matrix_status, f"{pillar_id}: missing matrix_status in matrix row."
        roadmap_row = _extract_pillar_row(roadmap_text, pillar_id)
        if pillar_id == "PILLAR-STAT" and "| `ACTIVE` |" in roadmap_row:
            assert matrix_status in {"ACTIVE", "CLOSED"}, (
                "PILLAR-STAT staged handoff may present ACTIVE roadmap posture with CLOSED matrix status."
            )
        else:
            assert f"| `{matrix_status}` |" in roadmap_row, f"{pillar_id}: roadmap status row must match matrix_status."
