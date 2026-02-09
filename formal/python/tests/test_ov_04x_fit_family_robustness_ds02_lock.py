from __future__ import annotations

import json
import re
from pathlib import Path

from formal.python.toe.observables.ov04x_fit_family_robustness_record import ov04x_fit_family_robustness_report


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


def _extract_report_fingerprint(md_text: str) -> str:
    m = re.search(r"Report fingerprint:\s*`([0-9a-f]{64})`", md_text)
    if m is None:
        raise AssertionError("Missing report fingerprint line")
    return m.group(1)


def test_ov_04x_lock_matches_computed_report():
    rep = ov04x_fit_family_robustness_report(repo_root=REPO_ROOT)

    lock_path = (
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-04x_fit_family_robustness_DS02_lowk.md"
    )
    text = lock_path.read_text(encoding="utf-8")
    locked = _extract_json_block(text)

    # JSON payload is the report fields.
    assert locked.get("config_tag") == rep.config_tag
    assert locked.get("adequacy_policy") == rep.adequacy_policy
    assert bool(locked.get("prefer_curved")) == bool(rep.prefer_curved)
    assert bool(locked.get("robustness_failed")) == bool(rep.robustness_failed)

    # Locked fingerprint must match computed fingerprint.
    assert _extract_report_fingerprint(text) == rep.fingerprint()
