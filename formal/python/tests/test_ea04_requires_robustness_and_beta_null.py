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


def _first_field(block: str, field: str) -> str | None:
    prefix = f"{field}:"
    for line in block.splitlines():
        if line.startswith(prefix):
            return line[len(prefix) :].strip()
    return None


def test_ea04_policy_and_application_remain_beta_null_and_robustness_only():
    doc = (REPO_ROOT / "State_of_the_Theory.md").read_text(encoding="utf-8")

    ea04 = _extract_block(doc, block_id="EA-04")
    ea04a = _extract_block(doc, block_id="EA-04a")

    ea04_lower = ea04.lower()
    assert "robust" in ea04_lower
    assert "β" in ea04_lower or "beta" in ea04_lower
    assert ("not inferred" in ea04_lower) or ("compatible with 0" in ea04_lower) or ("not significant" in ea04_lower)

    # Forbid strong curvature language.
    forbidden = ["β≠0", "beta!=0", "detected curvature", "beta detected", "statistically significant beta"]
    for phrase in forbidden:
        assert phrase not in ea04_lower

    # Application record must stay evidence-only and beta-null.
    ea04a_lower = ea04a.lower()
    assert "robust" in ea04a_lower
    assert ("not inferred" in ea04a_lower) or ("compatible with 0" in ea04a_lower) or ("not significant" in ea04a_lower)
