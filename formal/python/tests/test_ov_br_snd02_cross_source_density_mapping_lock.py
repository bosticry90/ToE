from __future__ import annotations

import json
import re
from pathlib import Path

from formal.python.toe.observables.ovbr_snd02_cross_source_density_mapping_record import (
    ovbr_snd02_cross_source_density_mapping_record,
)


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
        raise AssertionError("Missing JSON record block")
    return json.loads(m.group(1))


def _extract_record_fingerprint(md_text: str) -> str:
    m = re.search(r"Record fingerprint:\s*`([0-9a-f]{64})`", md_text)
    if m is None:
        raise AssertionError("Missing record fingerprint line")
    return m.group(1)


def test_ov_br_snd02_lock_matches_computed_record() -> None:
    rec = ovbr_snd02_cross_source_density_mapping_record(date="2026-01-24")

    lock_path = (
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-BR-SND-02_cross_source_density_mapping.md"
    )

    text = lock_path.read_text(encoding="utf-8")
    locked = _extract_json_block(text)

    assert locked == rec.to_jsonable()
    assert _extract_record_fingerprint(text) == rec.fingerprint()

    assert locked["mapping"]["status"] == "unblocked"
    assert locked["mapping"]["mapping_is_complete"] is True
    assert isinstance(locked["mapping"].get("mapping_tuples"), list)
    assert len(locked["mapping"].get("mapping_tuples") or []) >= 2
