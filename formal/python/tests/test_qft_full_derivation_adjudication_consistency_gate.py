from __future__ import annotations

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
QFT_DISCHARGE_DOC_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md"
)
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def _extract_token_from_surfaces(token_name: str, *surfaces: str) -> str:
    for surface in surfaces:
        m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", surface)
        if m is not None:
            return m.group(1)
    assert False, f"Missing token `{token_name}` across authority surfaces."


def test_qft_full_derivation_adjudication_tokens_are_consistent_across_authority_surfaces() -> None:
    canonical_text = _read(QFT_DISCHARGE_DOC_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    canonical_adjudication = _extract_token(canonical_text, "QFT_FULL_DERIVATION_ADJUDICATION")
    canonical_inevitability = _extract_token(canonical_text, "QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION")

    state_or_inventory_adjudication = _extract_token_from_surfaces(
        "QFT_FULL_DERIVATION_ADJUDICATION", state_text, inventory_text, roadmap_text
    )
    state_or_inventory_inevitability = _extract_token_from_surfaces(
        "QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION", state_text, inventory_text, roadmap_text
    )

    roadmap_adjudication = _extract_token(roadmap_text, "QFT_FULL_DERIVATION_ADJUDICATION")
    roadmap_inevitability = _extract_token(roadmap_text, "QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION")

    assert canonical_adjudication == state_or_inventory_adjudication == roadmap_adjudication
    assert canonical_inevitability == state_or_inventory_inevitability == roadmap_inevitability
    assert canonical_adjudication == "DISCHARGED_v0"
    assert canonical_inevitability == "DISCHARGED_v0"
