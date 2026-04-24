from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
STATE_CORE_PATH = REPO_ROOT / "formal" / "docs" / "release" / "state_core_v0.json"
RENDERER_PATH = REPO_ROOT / "formal" / "python" / "tools" / "render_state_core_mirrors.py"

STATE_SNIPPET = REPO_ROOT / "formal" / "output" / "state_core_generated" / "state_core_state_snippet_v0.md"
ROADMAP_SNIPPET = REPO_ROOT / "formal" / "output" / "state_core_generated" / "state_core_roadmap_snippet_v0.md"
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
        "Renderer apply/verify failed for WS-10 branch status family gate.\n"
        f"stdout:\n{completed.stdout}\n"
        f"stderr:\n{completed.stderr}"
    )


def test_ws10_branch_boundary_status_family_contract() -> None:
    state_core = json.loads(STATE_CORE_PATH.read_text(encoding="utf-8"))

    family = state_core["ws10_branch_boundary_status_family"]
    assert family["family_id"] == "WS10_BRANCH_BOUNDARY_AUTHORIZATION_STATUS_v0"
    assert family["active_decision_id"] == "WS-10-T19"

    chain = family["decision_chain"]
    assert len(chain) >= 9

    decision_ids = [entry["id"] for entry in chain]
    assert decision_ids[0] == "WS-10-T11"
    assert decision_ids[-1] == "WS-10-T19"
    assert family["active_decision_id"] in decision_ids

    for entry in chain:
        assert entry["kind"] in {"branch_authorization", "boundary_stop"}
        decision_artifact = REPO_ROOT / entry["decision_artifact"]
        assert decision_artifact.exists(), f"Missing decision artifact: {decision_artifact}"


def test_ws10_branch_boundary_status_family_renderer_surface_coverage() -> None:
    _run_renderer()

    state_text = STATE_SNIPPET.read_text(encoding="utf-8")
    roadmap_text = ROADMAP_SNIPPET.read_text(encoding="utf-8")
    tracker_text = TRACKER_SNIPPET.read_text(encoding="utf-8")
    ws10_text = WS10_SNIPPET.read_text(encoding="utf-8")

    assert "STATE_CORE_BRANCH_BOUNDARY_ACTIVE_DECISION_v0: WS-10-T19" in state_text
    assert "STATE_CORE_BRANCH_BOUNDARY_ACTIVE_STATUS_v0: STOPPED_AT_CYCLE10_TO_11_SYNTHESIS_BOUNDARY_v0" in state_text

    assert "STATE_CORE_ROADMAP_BRANCH_CHAIN_v0:" in roadmap_text
    assert "WS-10-T11:branch_authorization" in roadmap_text
    assert "WS-10-T19:boundary_stop" in roadmap_text

    assert "STATE_CORE_TRACKER_BRANCH_DECISION_v0: WS-10-T19" in tracker_text
    assert "STATE_CORE_TRACKER_BRANCH_STATUS_v0: STOPPED_AT_CYCLE10_TO_11_SYNTHESIS_BOUNDARY_v0" in tracker_text

    assert "STATE_CORE_WS10_ACTIVE_DECISION_v0: WS-10-T19" in ws10_text
    assert "STATE_CORE_WS10_BRANCH_CHAIN_v0:" in ws10_text
