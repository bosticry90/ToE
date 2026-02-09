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
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"


def _extract_gap_blocks(text: str, *, gap_id: str) -> list[str]:
    marker_re = re.compile(rf"^GapID:\s*{re.escape(gap_id)}\s*$", flags=re.MULTILINE)
    blocks: list[str] = []
    for m in marker_re.finditer(text):
        start = m.start()
        nxt = re.search(r"^GapID:\s*\S+\s*$", text[m.end() :], flags=re.MULTILINE)
        if nxt is None:
            blocks.append(text[start:])
        else:
            blocks.append(text[start : m.end() + nxt.start()])
    if not blocks:
        raise AssertionError(f"Could not find exact gap marker for GapID: {gap_id!r}")
    return blocks


def _first_field(block: str, field: str) -> str | None:
    prefix = f"{field}:"
    for line in block.splitlines():
        if line.startswith(prefix):
            return line[len(prefix) :].strip()
    return None


def test_comp03_is_implemented_and_comp05_is_lifted():
    text = STATE_PATH.read_text(encoding="utf-8")

    comp03_blocks = _extract_gap_blocks(text, gap_id="COMP-03")
    comp05_blocks = _extract_gap_blocks(text, gap_id="COMP-05")
    assert len(comp03_blocks) == 1, "Expected exactly one COMP-03 block; remove duplicates."
    assert len(comp05_blocks) == 1, "Expected exactly one COMP-05 block; remove duplicates."
    comp03 = comp03_blocks[0]
    comp05 = comp05_blocks[0]

    status03 = _first_field(comp03, "Status") or ""
    assert "Implemented" in status03
    assert "deferred" not in status03.lower()

    evidence03 = _first_field(comp03, "Evidence path") or ""
    for token in [
        "formal/python/toe/comparators/cv03_ucff_dispersion_v1.py",
        "formal/python/tests/test_cv03_ucff_dispersion_v1_front_door.py",
        "formal/python/tests/test_cv03_ucff_dispersion_v1_surface_contract_freeze.py",
        "formal/docs/cv03_ucff_dispersion_v1_front_door_contract.md",
    ]:
        assert token in evidence03, f"Missing COMP-03 evidence token: {token}"

    status05 = _first_field(comp05, "Status") or ""
    assert "Lifted" in status05
    assert "Active" not in status05
    scope05 = _first_field(comp05, "Scope") or ""
    assert "COMP-03/OV-CV-03" in scope05
    assert "UCFF" in scope05


def test_comp_pred_fals_mentions_cv03_ucff_lane():
    text = STATE_PATH.read_text(encoding="utf-8")
    blocks = _extract_gap_blocks(text, gap_id="COMP-PRED-FALS")
    assert len(blocks) == 1, "Expected exactly one COMP-PRED-FALS block; remove duplicates."
    block = blocks[0]
    evidence = _first_field(block, "Evidence path") or ""
    required_tokens = [
        "formal/python/toe/comparators/cv03_ucff_dispersion_v1.py",
        "formal/python/tests/test_cv03_ucff_dispersion_v1_front_door.py",
        "formal/python/tests/test_cv03_ucff_dispersion_v1_surface_contract_freeze.py",
        "formal/docs/cv03_ucff_dispersion_v1_front_door_contract.md",
    ]
    for token in required_tokens:
        assert token in evidence, f"Missing COMP-PRED-FALS evidence token for CV03 lane: {token}"
