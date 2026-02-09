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


def _extract_block(text: str, *, block_id: str) -> str:
    marker_re = re.compile(rf"^ID:\s*{re.escape(block_id)}\s*$", flags=re.MULTILINE)
    m = marker_re.search(text)
    if m is None:
        raise AssertionError(f"Could not find exact block marker for ID: {block_id!r}")
    start = m.start()

    next_idx = text.find("\n\n\nID:", start + 1)
    if next_idx < 0:
        return text[start:]
    return text[start:next_idx]


def _dependencies_line(block_text: str) -> str:
    for line in block_text.splitlines():
        if line.startswith("Dependencies:"):
            return line
    raise AssertionError("No Dependencies: line found in block")


def test_ea03_exists_and_encodes_frozen_robustness_and_beta_non_inference():
    doc = (REPO_ROOT / "State_of_the_Theory.md").read_text(encoding="utf-8")

    ea03 = _extract_block(doc, block_id="EA-03")
    deps = _dependencies_line(ea03)

    # Required wiring
    assert "OV-03x" in deps
    assert "DR-β-02" in deps

    lower = ea03.lower()

    # Required content keywords
    assert "frozen" in lower
    assert "robust" in lower

    # Must explicitly encode beta non-inference posture
    assert ("β not inferred" in lower) or ("compatible with 0" in lower) or ("not significant" in lower)

    # Must not use forbidden curvature-claim phrasing
    forbidden = re.compile(
        r"(\bβ\s*(?:!=|≠)\s*0\b|\bbeta\s*(?:!=|≠)\s*0\b|\bdetected\s+curvature\b|\bcurvature\s+detected\b)",
        re.IGNORECASE,
    )
    assert not forbidden.search(ea03), "EA-03 must not contain β!=0 / detected curvature phrasing"
