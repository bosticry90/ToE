from __future__ import annotations

import json
import re
from pathlib import Path

from formal.python.toe.observables.ovsw01_shallow_water_lowk_slope_record import (
    ovsw01_shallow_water_lowk_slope_record,
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


def test_ov_sw01_lock_exists_and_is_blocked_until_digitized_csv_exists() -> None:
    rec = ovsw01_shallow_water_lowk_slope_record(date="2026-01-25")

    assert bool(rec.status.get("blocked")) is True
    blockers = list(rec.status.get("blockers", []))
    assert "omega_over_2pi_vs_k_lowk_csv_missing" in blockers
    assert "omega_over_2pi_vs_k_lowk_metadata_missing" in blockers
    assert rec.results is None

    lock_path = (
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-SW-01_shallow_water_lowk_slope.md"
    )
    lock_text = lock_path.read_text(encoding="utf-8")
    locked = _extract_json_block(lock_text)

    assert locked == rec.to_jsonable()
    assert _extract_record_fingerprint(lock_text) == rec.fingerprint()
