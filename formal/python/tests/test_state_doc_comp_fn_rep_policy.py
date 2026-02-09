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


def test_comp_fn_rep_policy_is_wired_and_evidenced():
    text = STATE_PATH.read_text(encoding="utf-8")
    required_tokens = [
        "formal/toe_formal/ToeFormal/Variational/FNRepresentationEquivalencePolicy.lean",
        "formal/toe_formal/ToeFormal/Variational/ActionRep64CubicLane.lean",
        "formal/toe_formal/ToeFormal/Variational/DischargeELMatchesFN01Rep64Pcubic.lean",
        "formal/python/tests/test_lean_fn01_rep64_build_guard.py",
        "formal/python/tests/test_comparator_rep_policy_gate.py",
        "formal/python/toe/constraints/fn_rep_equivalence_policy.json",
        "formal/python/toe/comparators/comparator_rep_interpretability_manifest.json",
    ]
    blocks = _extract_gap_blocks(text, gap_id="COMP-FN-REP")
    matched = False
    for block in blocks:
        status = _first_field(block, "Status") or ""
        evidence = _first_field(block, "Evidence path") or ""
        notes = _first_field(block, "Notes") or ""

        if "In progress" not in status:
            continue
        if "Rep64 lane build-verified" not in status:
            continue
        if any(token not in evidence for token in required_tokens):
            continue
        if "within_rep_only" not in notes:
            continue
        if "FN_REP_EQ_POLICY_V1" not in notes:
            continue
        matched = True
        break

    assert matched, "No COMP-FN-REP block matched the expected Rep64 policy/evidence wiring."
