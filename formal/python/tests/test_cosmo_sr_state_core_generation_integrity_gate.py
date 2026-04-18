from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
RENDERER_PATH = REPO_ROOT / "formal" / "python" / "tools" / "render_state_core_mirrors.py"
STATE_CORE_PATH = REPO_ROOT / "formal" / "docs" / "release" / "state_core_v0.json"
STATE_SNIPPET_PATH = REPO_ROOT / "formal" / "output" / "state_core_generated" / "state_core_state_snippet_v0.md"


def _run_renderer_verify() -> None:
    cmd = [
        sys.executable,
        str(RENDERER_PATH),
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
        "Renderer verify failed for COSMO-SR aggregate integrity check.\n"
        f"stdout:\n{completed.stdout}\n"
        f"stderr:\n{completed.stderr}"
    )


def test_cosmo_sr_state_core_chain_and_renderer_integrity() -> None:
    state_core = json.loads(STATE_CORE_PATH.read_text(encoding="utf-8"))

    assert "COSMO_SR" in state_core["recent_tranche_chain_by_lane"]
    cosmo_chain = state_core["recent_tranche_chain_by_lane"]["COSMO_SR"]
    assert len(cosmo_chain) >= 2
    assert "WS-10-T10" in cosmo_chain
    assert "WS-10-T11" in cosmo_chain

    _run_renderer_verify()

    assert STATE_SNIPPET_PATH.exists(), "Missing generated state snippet output."
    snippet = STATE_SNIPPET_PATH.read_text(encoding="utf-8")
    assert "STATE_CORE_QUEUED_LANE_DETAILS_v0" in snippet
    assert "COSMO_SR:PAUSED@CYCLE08" in snippet
    assert "STATE_CORE_QUEUED_CHAIN_v0" in snippet
    assert "COSMO_SR=WS-10-T10,WS-10-T11" in snippet
