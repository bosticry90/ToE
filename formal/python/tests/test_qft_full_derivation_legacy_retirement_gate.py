from __future__ import annotations

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
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
QFT_DISCHARGE_DOC_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md"
)


LEGACY_QFT_ADJUDICATION_TOKEN = "QFT_FULL_DERIVATION_ADJUDICATION: NOT_YET_DISCHARGED"
LEGACY_QFT_INEVITABILITY_TOKEN = "QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION: NOT_YET_DISCHARGED"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qft_legacy_not_yet_adjudication_token_is_retired_from_active_authority_surfaces() -> None:
    state_text, _ = split_active_and_archived(_read(STATE_PATH), STATE_PATH)
    roadmap_text, _ = split_active_and_archived(_read(ROADMAP_PATH), ROADMAP_PATH)
    discharge_text, _ = split_active_and_archived(_read(QFT_DISCHARGE_DOC_PATH), QFT_DISCHARGE_DOC_PATH)

    assert LEGACY_QFT_ADJUDICATION_TOKEN not in state_text, "Legacy QFT adjudication token present in active State authority surface."
    assert LEGACY_QFT_INEVITABILITY_TOKEN not in state_text, "Legacy QFT inevitability token present in active State authority surface."
    assert LEGACY_QFT_ADJUDICATION_TOKEN not in roadmap_text, "Legacy QFT adjudication token present in roadmap authority surface."
    assert LEGACY_QFT_INEVITABILITY_TOKEN not in roadmap_text, "Legacy QFT inevitability token present in roadmap authority surface."
    assert LEGACY_QFT_ADJUDICATION_TOKEN not in discharge_text, "Legacy QFT adjudication token present in discharge authority surface."
    assert LEGACY_QFT_INEVITABILITY_TOKEN not in discharge_text, "Legacy QFT inevitability token present in discharge authority surface."
