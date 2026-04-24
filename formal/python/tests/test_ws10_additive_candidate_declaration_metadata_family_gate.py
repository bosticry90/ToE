from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

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
        "Renderer apply/verify failed for WS-10 additive-candidate declaration metadata family gate.\n"
        f"stdout:\n{completed.stdout}\n"
        f"stderr:\n{completed.stderr}"
    )


def test_ws10_additive_candidate_declaration_metadata_family_contract() -> None:
    state_core = json.loads(STATE_CORE_PATH.read_text(encoding="utf-8"))

    family = state_core["ws10_additive_candidate_declaration_metadata_family"]
    assert family["family_id"] == "WS10_ADDITIVE_CANDIDATE_DECLARATION_METADATA_v0"
    assert family["active_candidate_id"] == "WS10-AC18-QM_STAT_CYCLE11"

    entries = family["entries"]
    assert len(entries) >= 8

    candidate_ids = [entry["candidate_id"] for entry in entries]
    assert candidate_ids[0] == "WS10-AC12-QM_STAT_CYCLE08"
    assert candidate_ids[-1] == "WS10-AC18-COSMO_SR_CYCLE08"
    assert family["active_candidate_id"] in candidate_ids

    lane_values = {entry["lane"] for entry in entries}
    assert lane_values == {"QM_STAT", "COSMO_SR"}

    for entry in entries:
        assert entry["cycle_target"].startswith("CYCLE")
        assert entry["status_token"].endswith("DECLARED_BOUNDED_NONREDUNDANT_PAYLOAD_v0")
        decision_linkage = REPO_ROOT / entry["decision_linkage"]
        artifact_pointer = REPO_ROOT / entry["artifact_pointer"]
        assert decision_linkage.exists(), f"Missing decision linkage path: {decision_linkage}"
        assert artifact_pointer.exists(), f"Missing artifact pointer path: {artifact_pointer}"


def test_ws10_additive_candidate_declaration_metadata_family_renderer_surface_coverage() -> None:
    _run_renderer()

    tracker_text = TRACKER_SNIPPET.read_text(encoding="utf-8")
    ws10_text = WS10_SNIPPET.read_text(encoding="utf-8")

    assert "STATE_CORE_TRACKER_WS10_ADDITIVE_CANDIDATE_ACTIVE_ID_v0: WS10-AC18-QM_STAT_CYCLE11" in tracker_text
    assert "STATE_CORE_TRACKER_WS10_ADDITIVE_CANDIDATE_ACTIVE_LANE_v0: QM_STAT" in tracker_text
    assert "STATE_CORE_TRACKER_WS10_ADDITIVE_CANDIDATE_ENTRY_COUNT_v0: 8" in tracker_text

    assert "STATE_CORE_WS10_ADDITIVE_CANDIDATE_ACTIVE_ID_v0: WS10-AC18-QM_STAT_CYCLE11" in ws10_text
    assert "STATE_CORE_WS10_ADDITIVE_CANDIDATE_ACTIVE_LANE_v0: QM_STAT" in ws10_text
    assert "STATE_CORE_WS10_ADDITIVE_CANDIDATE_ENTRY_COUNT_v0: 8" in ws10_text
    assert "STATE_CORE_WS10_ADDITIVE_CANDIDATE_CHAIN_v0: WS10-AC12-QM_STAT_CYCLE08:QM_STAT:CYCLE08" in ws10_text
