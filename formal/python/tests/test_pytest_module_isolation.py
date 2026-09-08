from __future__ import annotations

import subprocess
from pathlib import Path

from formal.python.tools.pytest_module_isolation import isolate_pytest_modules


def _git(repo: Path, *args: str) -> None:
    subprocess.run(["git", *args], cwd=repo, check=True, capture_output=True)


def _repo(tmp_path: Path) -> Path:
    _git(tmp_path, "init")
    source = tmp_path / "source.txt"
    source.write_text("clean\n", encoding="utf-8", newline="\n")
    _git(tmp_path, "add", "source.txt")
    return source


def test_module_failures_are_classified_without_becoming_cascades(tmp_path: Path) -> None:
    _repo(tmp_path)
    returns = iter([1, 0])

    def runner(command: list[str], **_: object) -> subprocess.CompletedProcess[str]:
        returncode = next(returns)
        return subprocess.CompletedProcess(command, returncode, "module output", "")

    result = isolate_pytest_modules(
        ["first.py", "second.py"], repo_root=tmp_path, runner=runner
    )
    assert result["results"][0]["failure_class"] == "PRIMARY_COMMITTED_DEFECT"
    assert result["results"][1]["status"] == "PASSED"
    assert result["modules_completed"] == 2


def test_source_mutation_stops_before_cross_module_contamination(tmp_path: Path) -> None:
    source = _repo(tmp_path)
    calls = 0

    def runner(command: list[str], **_: object) -> subprocess.CompletedProcess[str]:
        nonlocal calls
        calls += 1
        source.write_text("mutated\n", encoding="utf-8", newline="\n")
        return subprocess.CompletedProcess(command, 0, "", "")

    result = isolate_pytest_modules(
        ["mutator.py", "victim.py"], repo_root=tmp_path, runner=runner
    )
    assert calls == 1
    assert result["results"][0]["failure_class"] == "ORDER_DEPENDENT_CONTAMINATION"
    assert result["unexecuted_after_mutation"] == ["victim.py"]
