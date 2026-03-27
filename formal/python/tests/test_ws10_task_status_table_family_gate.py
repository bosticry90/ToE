from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
STATE_CORE_PATH = REPO_ROOT / "formal" / "docs" / "release" / "state_core_v0.json"
RENDERER_PATH = REPO_ROOT / "formal" / "python" / "tools" / "render_state_core_mirrors.py"

TRACKER_SNIPPET = REPO_ROOT / "formal" / "output" / "state_core_generated" / "state_core_tracker_snippet_v0.md"
WS10_SNIPPET = REPO_ROOT / "formal" / "output" / "state_core_generated" / "state_core_ws10_snippet_v0.md"


def _run_renderer() -> None:
    cmd = [
        sys.executable,
        str(RENDERER_PATH),
        "--apply-mirrors",
        "--verify-mirrors",
    ]
    completed = subprocess.run(
        cmd,
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert completed.returncode == 0, (
        "Renderer apply/verify failed for WS-10 task status family gate.\n"
        f"stdout:\n{completed.stdout}\n"
        f"stderr:\n{completed.stderr}"
    )


def test_ws10_task_status_table_family_contract() -> None:
    state_core = json.loads(STATE_CORE_PATH.read_text(encoding="utf-8"))

    family = state_core["ws10_task_status_table_family"]
    assert family["family_id"] == "WS10_TASK_STATUS_TABLE_v0"

    rows = family["rows"]
    assert len(rows) >= 19

    row_ids = [entry["id"] for entry in rows]
    assert row_ids[0] == "WS-10-T01"
    assert row_ids[-1] == "WS-10-T19"

    active_task_ids = family["active_task_ids"]
    assert sorted(active_task_ids) == ["WS-10-T07", "WS-10-T07B"]
    for task_id in active_task_ids:
        assert task_id in row_ids

    by_id = {entry["id"]: entry for entry in rows}
    assert by_id["WS-10-T01"]["blocked_by"] == "none"
    assert by_id["WS-10-T19"]["blocked_by"] == "WS-10-T18"


def test_ws10_task_status_table_family_renderer_surface_coverage() -> None:
    _run_renderer()

    tracker_text = TRACKER_SNIPPET.read_text(encoding="utf-8")
    ws10_text = WS10_SNIPPET.read_text(encoding="utf-8")

    assert "STATE_CORE_TRACKER_WS10_ACTIVE_TASKS_v0: WS-10-T07, WS-10-T07B" in tracker_text
    assert "STATE_CORE_TRACKER_WS10_TASK_ROWS_v0: 21" in tracker_text
    assert "STATE_CORE_TRACKER_WS10_DONE_TASKS_v0: 19" in tracker_text

    assert "STATE_CORE_WS10_ACTIVE_TASKS_v0: WS-10-T07, WS-10-T07B" in ws10_text
    assert "STATE_CORE_WS10_TASK_ROW_COUNT_v0: 21" in ws10_text
    assert "STATE_CORE_WS10_DONE_TASK_COUNT_v0: 19" in ws10_text
    assert "STATE_CORE_WS10_TASK_STATUS_CHAIN_v0:" in ws10_text
