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


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def _qft_roadmap_row(text: str) -> str:
    rows = [line.strip() for line in text.splitlines() if line.strip().startswith("| `PILLAR-QFT` |")]
    assert len(rows) == 1, f"Expected exactly one PILLAR-QFT row, found {len(rows)}."
    return rows[0]


def test_pillar_status_matrix_qft_entry_matches_all_authority_surfaces() -> None:
    matrix = _read_json(MATRIX_PATH)
    canonical_rel = matrix.get("canonical_source")
    assert isinstance(canonical_rel, str) and canonical_rel, "Matrix must declare canonical_source."

    canonical_path = REPO_ROOT / canonical_rel
    canonical_text = _read(canonical_path)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    qft_entry = matrix.get("pillars", {}).get("PILLAR-QFT", {})
    assert qft_entry, "Matrix must define PILLAR-QFT entry."

    canonical_adjudication = _extract_token(canonical_text, "QFT_FULL_DERIVATION_ADJUDICATION")
    canonical_inevitability = _extract_token(canonical_text, "QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION")

    assert qft_entry.get("full_derivation") == canonical_adjudication
    assert qft_entry.get("inevitability") == canonical_inevitability

    state_adjudication = _extract_token(state_text, "QFT_FULL_DERIVATION_ADJUDICATION")
    state_inevitability = _extract_token(state_text, "QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION")
    assert qft_entry.get("full_derivation") == state_adjudication
    assert qft_entry.get("inevitability") == state_inevitability

    qft_row = _qft_roadmap_row(roadmap_text)
    assert f"| `{qft_entry.get('matrix_status')}` |" in qft_row, "Roadmap matrix status must match pillar status matrix."
