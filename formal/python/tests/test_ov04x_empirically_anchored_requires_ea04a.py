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


def test_ov04x_empirically_anchored_is_gated_by_ea04a_record():
    doc = (REPO_ROOT / "State_of_the_Theory.md").read_text(encoding="utf-8")

    ov04x = _extract_block(doc, block_id="OV-04x")
    ea04a = _extract_block(doc, block_id="EA-04a")

    ov04x_status = _first_field(ov04x, "Status")
    assert ov04x_status is not None

    if ov04x_status == "Empirically Anchored":
        assert _first_field(ea04a, "Status") == "Evidence (Markdown)"

        lower = ea04a.lower()
        assert "ov-04x" in lower
        assert "robust" in lower
        assert ("β not inferred" in lower) or ("compatible with 0" in lower) or ("not significant" in lower)

        deps = _first_field(ov04x, "Dependencies") or ""
        assert "EA-04a" in deps
