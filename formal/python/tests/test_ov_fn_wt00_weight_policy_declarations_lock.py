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


def extract_json_block(md_text: str) -> dict:
    m = re.search(r"```json\s*(\{.*?\})\s*```", md_text, flags=re.DOTALL)
    if m is None:
        raise ValueError("Missing JSON record block")
    return json.loads(m.group(1))


REPO_ROOT = find_repo_root(Path(__file__))


def test_ov_fn_wt00_weight_policy_declarations_lock_schema_and_rows() -> None:
    lock_path = (
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-FN-WT-00_fn01_weight_policy_declarations.md"
    )
    assert lock_path.exists()

    locked = extract_json_block(lock_path.read_text(encoding="utf-8"))
    assert locked["schema"] == "OV-FN-WT-00_fn01_weight_policy_declarations/v1"
    assert locked["observable_id"] == "OV-FN-WT-00"

    rows = list(locked.get("rows") or [])
    assert len(rows) >= 2
    assert all(isinstance(r.get("policy_id"), str) for r in rows)
    assert all(isinstance(r.get("fn_candidate_id"), str) for r in rows)
