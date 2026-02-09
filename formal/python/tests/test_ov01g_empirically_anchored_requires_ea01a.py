from __future__ import annotations

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
    marker = f"ID: {block_id}"
    start = text.find(marker)
    if start < 0:
        raise AssertionError(f"Could not find block marker: {marker!r}")

    next_idx = text.find("\n\n\nID:", start + len(marker))
    if next_idx < 0:
        return text[start:]
    return text[start:next_idx]


def _first_field(block: str, field: str) -> str | None:
    prefix = f"{field}:"
    for line in block.splitlines():
        if line.startswith(prefix):
            return line[len(prefix) :].strip()
    return None


def test_ov01g_empirically_anchored_is_gated_by_ea01a_record():
    doc = (REPO_ROOT / "State_of_the_Theory.md").read_text(encoding="utf-8")

    ov01g = _extract_block(doc, block_id="OV-01g")
    ea01a = _extract_block(doc, block_id="EA-01a")

    ov01g_status = _first_field(ov01g, "Status")
    assert ov01g_status is not None

    if ov01g_status == "Empirically Anchored":
        # Promotion record must exist.
        assert _first_field(ea01a, "Status") == "Evidence (Markdown)"

        # Promotion record should explicitly bind robustness-only + beta non-inference.
        ea01a_lower = ea01a.lower()
        assert "ov-01g" in ea01a_lower
        assert "robust" in ea01a_lower
        assert ("β not inferred" in ea01a_lower) or ("compatible with 0" in ea01a_lower) or ("differs from 0" in ea01a_lower)

        # OV-01g should depend on EA-01a to avoid silent upgrades.
        deps = _first_field(ov01g, "Dependencies") or ""
        assert "EA-01a" in deps
