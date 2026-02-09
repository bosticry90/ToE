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


def _extract_gap_block(text: str, *, gap_id: str) -> str:
    marker_re = re.compile(rf"^GapID:\s*{re.escape(gap_id)}\s*$", flags=re.MULTILINE)
    m = marker_re.search(text)
    if m is None:
        raise AssertionError(f"Could not find exact gap marker for GapID: {gap_id!r}")
    start = m.start()

    nxt = re.search(r"^GapID:\s*\S+\s*$", text[m.end() :], flags=re.MULTILINE)
    if nxt is None:
        return text[start:]
    return text[start : m.end() + nxt.start()]


def _first_field(block: str, field: str) -> str | None:
    prefix = f"{field}:"
    for line in block.splitlines():
        if line.startswith(prefix):
            return line[len(prefix) :].strip()
    return None


def test_comp_fn_rep32_link_is_marked_implemented_and_build_guarded():
    text = STATE_PATH.read_text(encoding="utf-8")
    block = _extract_gap_block(text, gap_id="COMP-FN-REP32-LINK")

    status = _first_field(block, "Status") or ""
    assert "Implemented" in status
    assert "build guard" in status

    evidence = _first_field(block, "Evidence path") or ""
    required_tokens = [
        "formal/toe_formal/ToeFormal/Variational/ActionRep32CubicLane.lean",
        "formal/toe_formal/ToeFormal/Variational/DischargeELMatchesFN01Rep32Pcubic.lean",
        "formal/python/tests/test_lean_fn01_rep32_build_guard.py",
        "formal/python/tests/test_fn01_candidate_api_enforced.py",
    ]
    for token in required_tokens:
        assert token in evidence, f"Missing COMP-FN-REP32-LINK evidence token: {token}"

    exit_criteria = _first_field(block, "Exit criteria") or ""
    assert "versioned" in exit_criteria
    assert "compile" in exit_criteria
