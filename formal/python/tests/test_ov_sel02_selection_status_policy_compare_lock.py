from __future__ import annotations

import json
import re
from pathlib import Path

from formal.python.toe.observables.ovsel02_selection_status_record import ovsel02_selection_status_record


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


def test_ov_sel02_lock_matches_computed() -> None:
    lock_path = REPO_ROOT / "formal" / "markdown" / "locks" / "observables" / "OV-SEL-02_selection_status_policy_compare.md"
    assert lock_path.exists(), f"Missing lock: {lock_path.as_posix()}"

    rec = ovsel02_selection_status_record().to_jsonable()

    text = lock_path.read_text(encoding="utf-8")
    locked = _extract_json_block(text)

    assert locked == rec
    assert _extract_record_fingerprint(text) == ovsel02_selection_status_record().fingerprint()


def test_ov_sel02_delta_is_only_ov03x() -> None:
    rec = ovsel02_selection_status_record().to_jsonable()
    changed = list(rec["delta"]["changed_observables"])
    assert changed == ["OV-03x"]
