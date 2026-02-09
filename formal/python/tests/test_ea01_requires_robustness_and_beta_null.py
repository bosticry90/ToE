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
    # Exact ID match (avoid prefix collisions like EA-01 vs EA-01a).
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


def test_ea01_exists_and_is_wired_to_robustness_and_beta_null():
    doc = (REPO_ROOT / "State_of_the_Theory.md").read_text(encoding="utf-8")

    ea01 = _extract_block(doc, block_id="EA-01")
    deps = _dependencies_line(ea01)

    # Required wiring
    assert "OV-01g" in deps
    assert "DR-β-01" in deps

    # Required content keywords (case-insensitive)
    lower = ea01.lower()
    assert "robust" in lower
    assert "frozen" in lower

    # Must explicitly encode the beta non-inference posture
    assert ("β not inferred" in lower) or ("compatible with 0" in lower) or ("not significant" in lower)

    # Must not use forbidden curvature-claim phrasing
    forbidden = re.compile(r"(\bβ\s*(?:!=|≠)\s*0\b|\bbeta\s*(?:!=|≠)\s*0\b|\bdetected\s+curvature\b|\bcurvature\s+detected\b)", re.IGNORECASE)
    assert not forbidden.search(ea01), "EA-01 must not contain β!=0 / detected curvature phrasing"
