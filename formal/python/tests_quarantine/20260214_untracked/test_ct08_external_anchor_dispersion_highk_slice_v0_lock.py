from __future__ import annotations

import json
import re
from pathlib import Path

from formal.python.toe.comparators.ct08_external_anchor_dispersion_highk_slice_v0 import (
    ct08_external_anchor_dispersion_highk_slice_v0_record,
    render_ct08_lock_markdown,
)


def _extract_json_block(md_text: str) -> dict:
    m = re.search(r"```json\s*(\{.*?\})\s*```", md_text, flags=re.DOTALL)
    assert m is not None
    return json.loads(m.group(1))


def test_ct08_lock_markdown_matches_record() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    lock_path = repo_root / "formal" / "markdown" / "locks" / "observables" / "CT-08_external_anchor_dispersion_highk_slice_v0.md"

    rec = ct08_external_anchor_dispersion_highk_slice_v0_record(date="2026-02-10", tolerance_profile="pinned")
    expected = render_ct08_lock_markdown(rec)

    md = lock_path.read_text(encoding="utf-8")
    assert md == expected

    payload = _extract_json_block(md)
    assert payload == rec.to_jsonable()
    assert f"Record fingerprint: `{rec.fingerprint()}`" in md
