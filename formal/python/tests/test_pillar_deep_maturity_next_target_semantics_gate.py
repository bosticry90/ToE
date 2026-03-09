from __future__ import annotations

import json
from pathlib import Path


TERMINAL_TOKEN = "TARGET-PHASE5-SR-M5-CONTROLLED-v0"
SR_ACTIVE_TOKEN = "TARGET-SR-M5-THEORY-PARITY-LINK-v0"


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_DEEP_MATURITY_REGISTRY_v0.json"


def _read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def test_pillar_deep_maturity_next_target_semantics_gate() -> None:
    registry = _read_json(REGISTRY_PATH)
    assert registry.get("sr_m5_completed_row_terminal_next_target_token") == TERMINAL_TOKEN

    rows = registry.get("pillars", [])
    assert isinstance(rows, list) and rows, "Missing deep maturity pillar rows."

    sr_rows = [row for row in rows if row.get("pillar_id") == "PILLAR-SR"]
    assert len(sr_rows) == 1, "Expected exactly one SR row in deep maturity registry."
    sr_row = sr_rows[0]

    assert sr_row.get("next_target") == SR_ACTIVE_TOKEN
    assert str(sr_row.get("m4_status", "")).startswith("COMPLETE")

    for row in rows:
        if row.get("pillar_id") == "PILLAR-SR":
            continue
        if str(row.get("m4_status", "")).startswith("COMPLETE"):
            assert row.get("next_target") == TERMINAL_TOKEN, (
                f"{row.get('pillar_id')}: complete non-SR rows must use terminal next_target token."
            )
