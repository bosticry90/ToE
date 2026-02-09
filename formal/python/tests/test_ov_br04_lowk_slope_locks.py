from __future__ import annotations

import json
import re
from pathlib import Path

from formal.python.toe.observables.ovbr04a_bragg_lowk_slope_conditionA_record import (
    ovbr04a_bragg_lowk_slope_conditionA_record,
)
from formal.python.toe.observables.ovbr04b_bragg_lowk_slope_conditionB_record import (
    ovbr04b_bragg_lowk_slope_conditionB_record,
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


def test_ov_br04a_lock_matches_computed_record() -> None:
    rec = ovbr04a_bragg_lowk_slope_conditionA_record(date="2026-01-25")

    lock_path = (
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-BR-04A_bragg_lowk_slope_conditionA.md"
    )
    lock_text = lock_path.read_text(encoding="utf-8")
    locked = _extract_json_block(lock_text)

    assert locked["schema"] == "OV-BR-04A_bragg_lowk_slope_conditionA/v2"
    assert locked["observable_id"] == "OV-BR-04A"
    assert locked["condition_key"] == "condition_A"

    assert locked == rec.to_jsonable()
    assert _extract_record_fingerprint(lock_text) == rec.fingerprint()


def test_ov_br04b_lock_matches_computed_record() -> None:
    rec = ovbr04b_bragg_lowk_slope_conditionB_record(date="2026-01-25")

    lock_path = (
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-BR-04B_bragg_lowk_slope_conditionB.md"
    )
    lock_text = lock_path.read_text(encoding="utf-8")
    locked = _extract_json_block(lock_text)

    assert locked["schema"] == "OV-BR-04B_bragg_lowk_slope_conditionB/v2"
    assert locked["observable_id"] == "OV-BR-04B"
    assert locked["condition_key"] == "condition_B"

    assert locked == rec.to_jsonable()
    assert _extract_record_fingerprint(lock_text) == rec.fingerprint()
