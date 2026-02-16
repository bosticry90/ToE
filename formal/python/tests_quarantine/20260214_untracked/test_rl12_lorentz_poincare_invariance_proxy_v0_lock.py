from __future__ import annotations

import json
import re
from pathlib import Path

from formal.python.toe.comparators.rl12_lorentz_poincare_invariance_proxy_v0 import (
    render_rl12_lock_markdown,
    rl12_lorentz_poincare_invariance_proxy_v0_record,
)


def _extract_json_block(md_text: str) -> dict:
    m = re.search(r"```json\s*(\{.*?\})\s*```", md_text, flags=re.DOTALL)
    assert m is not None
    return json.loads(m.group(1))


def test_rl12_lock_markdown_matches_record() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    lock_path = repo_root / "formal" / "markdown" / "locks" / "observables" / "OV-RL-12_lorentz_poincare_invariance_proxy_v0.md"

    rec = rl12_lorentz_poincare_invariance_proxy_v0_record(date="2026-02-09", tolerance_profile="pinned")
    expected = render_rl12_lock_markdown(rec)

    md = lock_path.read_text(encoding="utf-8")
    assert md == expected

    payload = _extract_json_block(md)
    assert payload == rec.to_jsonable()
    assert f"Record fingerprint: `{rec.fingerprint()}`" in md
