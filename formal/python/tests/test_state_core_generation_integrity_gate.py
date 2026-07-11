from __future__ import annotations

import subprocess
import sys
import copy
import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
RENDERER_PATH = REPO_ROOT / "formal" / "python" / "tools" / "render_state_core_mirrors.py"
STATE_CORE_PATH = REPO_ROOT / "formal" / "docs" / "release" / "state_core_v0.json"
SCHEMA_PATH = REPO_ROOT / "formal" / "docs" / "release" / "STATE_CORE_SCHEMA_v0.json"


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


def test_state_core_is_explicitly_historical_and_nonauthorizing() -> None:
    state_core = json.loads(STATE_CORE_PATH.read_text(encoding="utf-8"))
    schema = json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))
    assert state_core["authority_role"] == "HISTORICAL_WS10_SNAPSHOT_NONAUTHORIZING"
    assert state_core["schema_version"] == schema["schema_version"] == 2


def test_state_core_schema_version_mismatch_fails_closed() -> None:
    from formal.python.tools.render_state_core_mirrors import _validate_state_core

    state_core = json.loads(STATE_CORE_PATH.read_text(encoding="utf-8"))
    schema = json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))
    stale = copy.deepcopy(state_core)
    stale["schema_version"] -= 1
    try:
        _validate_state_core(schema, stale)
    except ValueError as error:
        assert "schema_version mismatch" in str(error)
    else:
        raise AssertionError("state-core version drift did not fail closed")


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
