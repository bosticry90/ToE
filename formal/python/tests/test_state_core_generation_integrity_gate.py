from __future__ import annotations

import subprocess
import sys
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
RENDERER_PATH = REPO_ROOT / "formal" / "python" / "tools" / "render_state_core_mirrors.py"
STATE_CORE_PATH = REPO_ROOT / "formal" / "docs" / "release" / "state_core_v0.json"


EXPECTED_MIRRORS = [
    REPO_ROOT / "State_of_the_Theory.md",
    REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md",
    REPO_ROOT / "formal" / "docs" / "release" / "REPO_REMEDIATION_MASTER_TRACKER_v0.md",
    REPO_ROOT / "formal" / "docs" / "release" / "WS_10_THEORY_RESTART_PILOT_PLAN_v0.md",
]


def test_state_core_generation_integrity_gate_assets_exist() -> None:
    assert RENDERER_PATH.exists(), "Missing renderer tool."
    assert STATE_CORE_PATH.exists(), "Missing state_core_v0.json."
    for path in EXPECTED_MIRRORS:
        assert path.exists(), f"Missing mirror surface: {path}"


def test_state_core_generation_integrity_gate_verify_mirrors() -> None:
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
        "Mirror integrity verification failed.\n"
        f"stdout:\n{completed.stdout}\n"
        f"stderr:\n{completed.stderr}"
    )
