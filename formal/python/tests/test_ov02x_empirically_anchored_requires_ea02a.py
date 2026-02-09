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
    # Exact ID match (avoid prefix collisions like EA-02 vs EA-02a).
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


def test_ov02x_empirically_anchored_is_gated_by_ea02a_record():
    doc = (REPO_ROOT / "State_of_the_Theory.md").read_text(encoding="utf-8")

    ov02x = _extract_block(doc, block_id="OV-02x")
    ea02a = _extract_block(doc, block_id="EA-02a")

    ov02x_status = _first_field(ov02x, "Status")
    assert ov02x_status is not None

    if ov02x_status == "Empirically Anchored":
        # Promotion record must exist.
        assert _first_field(ea02a, "Status") == "Evidence (Markdown)"

        # Promotion record should explicitly bind invariance-only + non-inference posture.
        lower = ea02a.lower()
        assert "ov-02x" in lower
        assert ("invariance" in lower) or ("digitization" in lower)
        assert ("β not inferred" in lower) or ("compatible with 0" in lower) or ("not significant" in lower)

        # OV-02x should depend on EA-02a to avoid silent upgrades.
        deps = _first_field(ov02x, "Dependencies") or ""
        assert "EA-02a" in deps
