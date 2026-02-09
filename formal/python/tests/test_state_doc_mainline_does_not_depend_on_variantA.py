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

    # Find the next block delimiter (blank lines + ID:) after this marker.
    next_idx = text.find("\n\n\nID:", start + len(marker))
    if next_idx < 0:
        return text[start:]
    return text[start:next_idx]


def _dependencies_line(block_text: str) -> str:
    for line in block_text.splitlines():
        if line.startswith("Dependencies:"):
            return line
    raise AssertionError("No Dependencies: line found in block")


def test_pol01_mainline_dependencies_do_not_include_variantA_or_ov01x():
    doc = (REPO_ROOT / "State_of_the_Theory.md").read_text(encoding="utf-8")

    pol_block = _extract_block(doc, block_id="POL-01")
    deps = _dependencies_line(pol_block)

    assert "DQ-01_variantA" not in deps
    assert "OV-01x" not in deps

    # Sanity: POL-01 should depend on OV-01g + DQ-01.
    assert "OV-01g" in deps
    assert "DQ-01" in deps
