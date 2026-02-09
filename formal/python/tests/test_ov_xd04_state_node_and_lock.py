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


def test_ov_xd04_exists_and_depends_on_overlap_band_and_inputs():
    doc = (REPO_ROOT / "State_of_the_Theory.md").read_text(encoding="utf-8")

    ov_xd04 = _extract_block(doc, block_id="OV-XD-04")

    assert _first_field(ov_xd04, "Category") == "Observable"
    assert _first_field(ov_xd04, "Status") in {"Locked", "Behavioral (Python)", "Empirically Anchored"}

    deps = _first_field(ov_xd04, "Dependencies") or ""
    for required in ["OV-XD-03", "OV-03x", "OV-04x"]:
        assert required in deps

    # Keep the scope guardrail intact.
    scope = (_first_field(ov_xd04, "Scope / limits") or "").lower()
    assert "overlap" in scope
    assert ("β" in scope) or ("beta" in scope) or ("null" in scope)


def test_ov_xd04_lock_exists_and_mentions_beta_null_posture():
    lock_path = (
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-XD-04_overlap_only_preference_comparison.md"
    )
    text = lock_path.read_text(encoding="utf-8").lower()

    assert "ov-xd-04" in text
    assert "ov-04x" in text
    assert "ov-03x" in text
    assert ("β" in text) or ("beta" in text) or ("beta-null" in text)
    assert ("not inferred" in text) or ("compatible with 0" in text) or ("beta-null" in text)
