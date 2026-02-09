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


def test_ov_xd01_exists_and_depends_on_anchored_observables():
    doc = (REPO_ROOT / "State_of_the_Theory.md").read_text(encoding="utf-8")

    ov_xd = _extract_block(doc, block_id="OV-XD-01")

    assert _first_field(ov_xd, "Category") == "Observable"
    assert _first_field(ov_xd, "Status") in {"Locked", "Behavioral (Python)", "Empirically Anchored"}

    deps = _first_field(ov_xd, "Dependencies") or ""
    for required in ["OV-01g", "OV-02x", "OV-03x"]:
        assert required in deps

    # Keep the scope guardrail intact.
    scope = (_first_field(ov_xd, "Scope / limits") or "").lower()
    assert "robust" in scope
    assert "inference" in scope or "must not" in scope


def test_ov_xd01_lock_exists_and_mentions_beta_null_posture():
    lock_path = (
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-XD-01_cross_dataset_robustness_agreement.md"
    )
    text = lock_path.read_text(encoding="utf-8").lower()

    assert "ov-xd-01" in text
    assert "ov-01g" in text
    assert "ov-02x" in text
    assert "ov-03x" in text
    assert "β" in text or "beta" in text
    assert ("not inferred" in text) or ("compatible with 0" in text) or ("beta-null" in text)
