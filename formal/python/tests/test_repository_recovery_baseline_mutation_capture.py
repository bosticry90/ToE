from __future__ import annotations

import subprocess
from pathlib import Path

from formal.python.tools import repository_recovery_baseline_mutation_capture as capture


def _git(repo: Path, *args: str) -> None:
    subprocess.run(["git", *args], cwd=repo, check=True, capture_output=True)


def test_capture_records_tracked_validation_mutation(tmp_path: Path) -> None:
    _git(tmp_path, "init")
    _git(tmp_path, "config", "user.name", "Recovery Test")
    _git(tmp_path, "config", "user.email", "recovery@example.invalid")
    _git(tmp_path, "config", "core.autocrlf", "false")
    source = tmp_path / "evidence.txt"
    source.write_text("before\n", encoding="utf-8", newline="\n")
    _git(tmp_path, "add", "evidence.txt")
    _git(tmp_path, "commit", "-m", "fixture")
    source.write_text("after\n", encoding="utf-8", newline="\n")

    manifest, diff = capture.build_manifest(tmp_path)

    assert manifest["tracked_dirty_count"] == 1
    assert manifest["untracked_count"] == 0
    assert manifest["classification"] == (
        "VALIDATION_COMMAND_MUTATED_BASELINE_CLONE"
    )
    assert manifest["entries"][0]["path"] == "evidence.txt"
    assert b"-before" in diff and b"+after" in diff
