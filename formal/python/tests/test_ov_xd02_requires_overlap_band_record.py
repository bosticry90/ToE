from __future__ import annotations

import json
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


def _extract_json_block(md_text: str) -> dict:
    m = re.search(r"```json\s*(\{.*?\})\s*```", md_text, flags=re.DOTALL)
    if m is None:
        raise AssertionError("Missing JSON block")
    return json.loads(m.group(1))


def test_ov_xd02_depends_on_ov_xd03_and_is_overlap_guarded():
    doc = (REPO_ROOT / "State_of_the_Theory.md").read_text(encoding="utf-8")

    ov_xd02 = _extract_block(doc, block_id="OV-XD-02")

    deps = _first_field(ov_xd02, "Dependencies") or ""
    assert "OV-XD-03" in deps

    # Load OV-XD-03 overlap record
    lock_xd03 = (
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-XD-03_cross_dataset_overlap_band_record.md"
    )
    xd03_text = lock_xd03.read_text(encoding="utf-8")
    xd03 = _extract_json_block(xd03_text)

    non_empty = bool(xd03.get("overlap", {}).get("non_empty"))

    # Enforcement policy:
    # - If overlap is non-empty, OV-XD-02 can be used as a cross-dataset record.
    # - If overlap is empty, OV-XD-02 must explicitly disclose that fact.
    if not non_empty:
        lock_xd02 = (
            REPO_ROOT
            / "formal"
            / "markdown"
            / "locks"
            / "observables"
            / "OV-XD-02_cross_dataset_preference_agreement_record.md"
        )
        t = lock_xd02.read_text(encoding="utf-8").lower()
        assert "no overlap" in t
        assert ("per-dataset" in t) or ("per dataset" in t)
