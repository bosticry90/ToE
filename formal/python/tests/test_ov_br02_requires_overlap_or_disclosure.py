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


def _extract_json_block(md_text: str) -> dict:
    m = re.search(r"```json\s*(\{.*?\})\s*```", md_text, flags=re.DOTALL)
    if m is None:
        raise AssertionError("Missing JSON block")
    return json.loads(m.group(1))


def test_ov_br02_requires_overlap_or_explicit_disclosure_and_tracks_ov_xd03_overlap():
    # Load OV-XD-03 overlap record (canonical authority).
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
    xd03_ov = xd03.get("overlap", {})

    # Load OV-BR-02 record (bridge).
    lock_br02 = (
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-BR-02_regime_bridge_record.md"
    )
    br02_text = lock_br02.read_text(encoding="utf-8")
    br02_lower = br02_text.lower()
    br02 = _extract_json_block(br02_text)

    overlap = br02.get("overlap")

    # Enforcement policy:
    # - If OV-XD-03 overlap is non-empty, OV-BR-02 must include an overlap band and
    #   it must match OV-XD-03 exactly (authoritative source).
    # - If OV-XD-03 overlap is empty, OV-BR-02 must explicitly disclose that
    #   comparison is not valid and that results are per-dataset only.
    if non_empty:
        assert isinstance(overlap, list) and len(overlap) == 2

        # Optional strictness (recommended): overlap equals OV-XD-03 overlap.
        assert float(overlap[0]) == float(xd03_ov.get("k_min"))
        assert float(overlap[1]) == float(xd03_ov.get("k_max"))

        # Also pin the overlap-only comparability phrase in the statement.
        cs = str(br02.get("comparability_statement", "")).lower()
        assert "overlap exists" in cs
        assert "overlap band" in cs
        assert "only within the ov-xd-03 overlap band" in cs
    else:
        cs = str(br02.get("comparability_statement", "")).lower()
        assert "no overlap" in cs
        assert "per-dataset" in cs

        # Either lock text or statement must be explicit about invalid comparison.
        assert ("comparison is not valid" in cs) or ("comparison is not valid" in br02_lower)
