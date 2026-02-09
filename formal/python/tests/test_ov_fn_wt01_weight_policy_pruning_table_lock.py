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


def test_ov_fn_wt01_weight_policy_pruning_table_lock_exists_and_is_blocked_by_default() -> None:
    lock_path = (
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-FN-WT-01_fn01_weight_policy_pruning_table.md"
    )
    assert lock_path.exists()

    locked = extract_json_block(lock_path.read_text(encoding="utf-8"))
    assert locked["schema"] == "OV-FN-WT-01_fn01_weight_policy_pruning_table/v1"
    assert locked["observable_id"] == "OV-FN-WT-01"

    # Default posture remains blocked (disabled gates).
    assert bool((locked.get("status") or {}).get("blocked")) is True

    rows = list(locked.get("rows") or [])
    assert len(rows) >= 2
    assert all(r.get("computed_under_blocked_admissibility") is True for r in rows)
