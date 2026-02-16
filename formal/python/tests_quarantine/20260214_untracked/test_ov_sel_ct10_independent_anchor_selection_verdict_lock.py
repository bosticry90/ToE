from __future__ import annotations

import json
import re
from pathlib import Path

from formal.python.toe.observables.ovselct10_independent_anchor_selection_verdict_record import (
    ovselct10_selection_verdict_record,
    render_ovselct10_lock_markdown,
)


def _extract_json_block(md_text: str) -> dict:
    m = re.search(r"```json\s*(\{.*?\})\s*```", md_text, flags=re.DOTALL)
    assert m is not None
    return json.loads(m.group(1))


def test_ov_sel_ct10_lock_markdown_matches_record() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    lock_path = (
        repo_root
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-SEL-CT10-01_independent_anchor_selection_verdict.md"
    )

    rec = ovselct10_selection_verdict_record(status_date="2026-02-12")
    expected = render_ovselct10_lock_markdown(rec)

    md = lock_path.read_text(encoding="utf-8")
    assert md == expected

    payload = _extract_json_block(md)
    assert payload == rec.to_jsonable()
    assert f"Record fingerprint: `{rec.fingerprint()}`" in md
