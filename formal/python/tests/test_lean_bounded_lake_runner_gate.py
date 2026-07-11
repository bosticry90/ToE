from __future__ import annotations

from pathlib import Path

import pytest

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import lean_bounded_lake as runner


REPO_ROOT = find_repo_root(Path(__file__))


def test_bounded_lake_command_uses_active_toolchain_scheduler() -> None:
    command = runner.bounded_lake_command(
        jobs=1, targets=["ToeFormal", "ToeFormalAll"], plan_only=True
    )
    assert command[:3] == ["lake", "--quiet", "--no-ansi"]
    assert command[-3:] == ["build", "ToeFormal", "ToeFormalAll"]
    assert "--no-build" in command
    assert runner.bounded_lake_environment(1)["LEAN_NUM_THREADS"] == "1"


def test_bounded_lake_command_rejects_unbounded_parallelism() -> None:
    with pytest.raises(ValueError, match="bounds exhaustive Lake scheduling"):
        runner.bounded_lake_command(jobs=3, targets=["ToeFormalAll"])
    with pytest.raises(ValueError, match="At least one Lake target"):
        runner.bounded_lake_command(jobs=1, targets=[])
    with pytest.raises(ValueError, match="bounds exhaustive Lake scheduling"):
        runner.bounded_lake_environment(3)


def test_ci_and_readmes_use_bounded_exhaustive_build() -> None:
    workflow = (REPO_ROOT / ".github" / "workflows" / "ci.yml").read_text(
        encoding="utf-8"
    )
    root_readme = (REPO_ROOT / "README.md").read_text(encoding="utf-8")
    development = (REPO_ROOT / "DEVELOPMENT.md").read_text(encoding="utf-8")
    lean_readme = (REPO_ROOT / "formal" / "toe_formal" / "README.md").read_text(
        encoding="utf-8"
    )
    module = "formal.python.tools.lean_bounded_lake"
    assert module in workflow
    assert module in root_readme
    assert module in development
    assert module in lean_readme
    assert "lake build ToeFormalAll" not in workflow
    assert "lake build ToeFormalAll" not in root_readme
    assert "lake build ToeFormalAll" not in development
    assert "lake build ToeFormalAll" not in lean_readme
