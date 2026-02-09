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


def test_comp_fn_rep_nonalias_equiv01_gap_is_wired() -> None:
    text = STATE_PATH.read_text(encoding="utf-8")
    blocks = _extract_gap_blocks(text, gap_id="COMP-FN-REP-NONALIAS-EQUIV-01")

    required_tokens = [
        "formal/toe_formal/ToeFormal/Variational/FNRepNonAliasEquivalence01.lean",
        "formal/python/tests/test_lean_fn_rep_nonalias_equivalence01_build_guard.py",
    ]
    required_notes = [
        "eligibleForCrossRep",
        "comparatorSurfaceNonAlias_eligible",
        "diagnosticNonAlias_not_eligible",
    ]

    matched = False
    for block in blocks:
        status = _first_field(block, "Status") or ""
        if "In progress" not in status:
            continue

        evidence = _first_field(block, "Evidence path") or ""
        if any(token not in evidence for token in required_tokens):
            continue

        notes = _first_field(block, "Notes") or ""
        if any(token not in notes for token in required_notes):
            continue

        matched = True
        break

    assert matched, "No COMP-FN-REP-NONALIAS-EQUIV-01 block matched expected status/evidence/notes."
    assert len(blocks) == 1, (
        "Expected exactly one COMP-FN-REP-NONALIAS-EQUIV-01 block; remove duplicates."
    )
