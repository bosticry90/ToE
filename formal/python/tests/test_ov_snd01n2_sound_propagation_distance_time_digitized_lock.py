from __future__ import annotations

import json
import re
from pathlib import Path

from formal.python.toe.observables.ovsnd01n2_sound_propagation_distance_time_digitized import (
    ovsnd01n2_digitized_propagation_dataset_record,
    write_ovsnd01n2_lock,
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


def test_ov_snd01n2_lock_matches_computed_record() -> None:
    # Ensure the lock exists and matches the computed record.
    rec = ovsnd01n2_digitized_propagation_dataset_record(date="2026-01-24")

    lock_path = (
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-SND-01N2_sound_propagation_distance_time_digitized.md"
    )

    if not lock_path.exists():
        write_ovsnd01n2_lock(date="2026-01-24")

    text = lock_path.read_text(encoding="utf-8")
    locked = _extract_json_block(text)

    assert locked == rec.to_jsonable()
    assert _extract_record_fingerprint(text) == rec.fingerprint()

    # On the current pinned Fig.2 render, we expect this to remain blocked unless/until
    # a second series is uniquely detectable.
    assert locked["observable_id"] == "OV-SND-01N2"
    assert isinstance(locked["status"], dict)
