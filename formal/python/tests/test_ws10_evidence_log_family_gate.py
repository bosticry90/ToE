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
        "Renderer apply/verify failed for WS-10 evidence-log family gate.\n"
        f"stdout:\n{completed.stdout}\n"
        f"stderr:\n{completed.stderr}"
    )


def test_ws10_evidence_log_family_contract() -> None:
    state_core = json.loads(STATE_CORE_PATH.read_text(encoding="utf-8"))

    family = state_core["ws10_evidence_log_family"]
    assert family["family_id"] == "WS10_EVIDENCE_LOG_CHECKPOINT_ENTRIES_v0"
    assert family["active_entry_id"] == "WS10-E19"

    entries = family["entries"]
    assert len(entries) >= 9

    entry_ids = [entry["id"] for entry in entries]
    assert entry_ids[0] == "WS10-E11"
    assert entry_ids[-1] == "WS10-E19"
    assert family["active_entry_id"] in entry_ids

    for entry in entries:
        assert entry["task_id"].startswith("WS-10-T")
        assert entry["date"].startswith("2026-03-")
        assert entry["checkpoint"]
        artifact = REPO_ROOT / entry["decision_artifact"]
        assert artifact.exists(), f"Missing decision artifact: {artifact}"


def test_ws10_evidence_log_family_renderer_surface_coverage() -> None:
    _run_renderer()

    tracker_text = TRACKER_SNIPPET.read_text(encoding="utf-8")
    ws10_text = WS10_SNIPPET.read_text(encoding="utf-8")

    assert "STATE_CORE_TRACKER_WS10_EVIDENCE_ACTIVE_ENTRY_v0: WS10-E19" in tracker_text
    assert "STATE_CORE_TRACKER_WS10_EVIDENCE_ACTIVE_TASK_v0: WS-10-T19" in tracker_text
    assert "STATE_CORE_TRACKER_WS10_EVIDENCE_ENTRY_COUNT_v0: 9" in tracker_text

    assert "STATE_CORE_WS10_EVIDENCE_ACTIVE_ENTRY_v0: WS10-E19" in ws10_text
    assert "STATE_CORE_WS10_EVIDENCE_ACTIVE_TASK_v0: WS-10-T19" in ws10_text
    assert "STATE_CORE_WS10_EVIDENCE_ENTRY_COUNT_v0: 9" in ws10_text
    assert "STATE_CORE_WS10_EVIDENCE_CHAIN_v0: WS10-E11:WS-10-T11" in ws10_text
