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


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def test_qft_full_derivation_adjudication_tokens_are_consistent_across_authority_surfaces() -> None:
    canonical_text = _read(QFT_DISCHARGE_DOC_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    canonical_adjudication = _extract_token(canonical_text, "QFT_FULL_DERIVATION_ADJUDICATION")
    canonical_inevitability = _extract_token(canonical_text, "QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION")

    state_adjudication = _extract_token(state_text, "QFT_FULL_DERIVATION_ADJUDICATION")
    state_inevitability = _extract_token(state_text, "QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION")

    roadmap_adjudication = _extract_token(roadmap_text, "QFT_FULL_DERIVATION_ADJUDICATION")
    roadmap_inevitability = _extract_token(roadmap_text, "QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION")

    assert canonical_adjudication == state_adjudication == roadmap_adjudication
    assert canonical_inevitability == state_inevitability == roadmap_inevitability
    assert canonical_adjudication == "DISCHARGED_v0"
    assert canonical_inevitability == "DISCHARGED_v0"
