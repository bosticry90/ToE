from __future__ import annotations

import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
STATE_DOC = REPO_ROOT / "State_of_the_Theory.md"
TAXONOMY_DOC = REPO_ROOT / "formal" / "docs" / "paper" / "CLAIM_TAXONOMY_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required artifact: {path.as_posix()}"
    return path.read_text(encoding="utf-8")


def _extract_inventory_block(text: str) -> str:
    start = text.find("Canonical claims inventory (paper-facing)")
    assert start >= 0, "Missing canonical claims inventory section."
    end = text.find("\n\n", start)
    if end < 0:
        end = len(text)
    # keep a wider slice to include bullets even with wrapped lines
    return text[start : min(len(text), end + 4000)]


def test_taxonomy_doc_exists_and_state_inventory_has_required_labels() -> None:
    taxonomy = _read(TAXONOMY_DOC)
    state = _read(STATE_DOC)
    inventory = _extract_inventory_block(state)

    assert "Claim Taxonomy v0" in taxonomy

    required_inventory_labels = [
        "T-CONDITIONAL",
        "E-REPRO",
        "P-POLICY",
        "B-BLOCKED",
    ]
    for label in required_inventory_labels:
        assert f"[{label}]" in inventory, f"State inventory missing required label: {label}"


def test_inventory_is_concise_and_paper_facing() -> None:
    state = _read(STATE_DOC)
    inventory = _extract_inventory_block(state)
    bullets = re.findall(r"^\s*-\s+\[[A-Z-]+\]", inventory, flags=re.MULTILINE)
    assert 10 <= len(bullets) <= 30, (
        "Canonical claims inventory should stay concise (10-30 bullets). "
        f"Found {len(bullets)} bullets."
    )
