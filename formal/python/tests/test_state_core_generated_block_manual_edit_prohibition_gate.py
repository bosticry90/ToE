from __future__ import annotations

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
POLICY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "STATE_CORE_GENERATED_FIRST_CUTOVER_POLICY_v0.md"
RENDERER_PATH = REPO_ROOT / "formal" / "python" / "tools" / "render_state_core_mirrors.py"


def test_state_core_generated_first_cutover_policy_exists_and_is_explicit() -> None:
    assert POLICY_PATH.exists(), "Missing generated-first cutover policy document."
    text = POLICY_PATH.read_text(encoding="utf-8")

    required_tokens = [
        "STATE_CORE_GENERATED_FIRST_CUTOVER_POLICY_v0",
        "Status: ACTIVE",
        "default canonical edit path",
        "Direct human edits inside generated marker blocks are prohibited.",
        "Edit `formal/docs/release/state_core_v0.json`.",
        "--apply-mirrors --verify-mirrors",
        "pwsh -NoProfile -ExecutionPolicy Bypass -File ./governance_suite.ps1",
        "Generated snippet artifacts are excluded from commit by default:",
        "formal/output/state_core_generated/state_core_tracker_snippet_v0.md",
        "formal/output/state_core_generated/state_core_ws10_snippet_v0.md",
        "Keep `manual_surface_compression_ratio >= 4.0`.",
        "Keep `governance_gate_default_enforced: true`.",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "Generated-first cutover policy missing required token(s): " + ", ".join(missing)


def test_state_core_generated_block_manual_edit_prohibition_gate() -> None:
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
        "Generated block verification failed. Direct human edits inside GENERATED blocks are prohibited. "
        "Update formal/docs/release/state_core_v0.json and rerun renderer.\n"
        f"stdout:\n{completed.stdout}\n"
        f"stderr:\n{completed.stderr}"
    )
