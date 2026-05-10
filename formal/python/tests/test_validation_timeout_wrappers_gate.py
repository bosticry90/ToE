from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
HELPER_PATH = REPO_ROOT / "validation_timeout_guard.ps1"
LEAN_WRAPPER_PATH = REPO_ROOT / "run_lean.ps1"
PYTEST_WRAPPER_PATH = REPO_ROOT / "run_pytest.ps1"
GOVERNANCE_WRAPPER_PATH = REPO_ROOT / "run_governance.ps1"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing validation timeout wrapper artifact: {path}"
    return path.read_text(encoding="utf-8")


def _assert_contains(content: str, needle: str) -> None:
    assert needle in content, f"Expected validation timeout wrapper contract text not found: {needle}"


def test_validation_timeout_guard_contract() -> None:
    content = _read(HELPER_PATH)

    for needle in [
        "$ValidationTimeoutExitCode = 124",
        "function Invoke-ValidationCommand",
        "function ConvertTo-ValidationProcessArgument",
        "function Get-ValidationProcessTree",
        "function Stop-ValidationProcessTree",
        "Start-Process",
        "Wait-Process",
        "-Timeout $TimeoutSeconds",
        "$stillRunning = Get-Process -Id $process.Id -ErrorAction SilentlyContinue",
        "if ($stillRunning)",
        "Get-CimInstance Win32_Process",
        "Stop-Process",
        "[System.IO.Path]::GetTempPath()",
        "elapsed_seconds",
        "validation_runner.DRY_RUN",
        "$startArgumentList",
    ]:
        _assert_contains(content, needle)


def test_lean_wrapper_contract() -> None:
    content = _read(LEAN_WRAPPER_PATH)

    for needle in [
        "[string]$Target = 'ToeFormal'",
        "[int]$TimeoutSeconds = 1800",
        "[int]$Threads = 0",
        "validation_timeout_guard.ps1",
        "formal\\toe_formal",
        "-FilePath 'lake'",
        "$lakeArgs = @()",
        "if ($Threads -gt 0)",
        '$lakeArgs += "-Kthreads=$Threads"',
        "$lakeArgs += @('build', $Target)",
        "-ArgumentList $lakeArgs",
        "-KillProcessNames @('lake', 'lean', 'elan')",
        "exit $exitCode",
    ]:
        _assert_contains(content, needle)


def test_pytest_wrapper_contract() -> None:
    content = _read(PYTEST_WRAPPER_PATH)

    for needle in [
        "[CmdletBinding(PositionalBinding = $false)]",
        "[int]$TimeoutSeconds = 1200",
        "[switch]$Parallel",
        "[string]$ParallelWorkers = 'auto'",
        "[string]$ParallelDist = 'loadfile'",
        "[Parameter(ValueFromRemainingArguments = $true)]",
        "formal/python/tests",
        "py.ps1",
        "'-m', 'pytest'",
        "$effectiveArgs += '-q'",
        "if ($LastFailed)",
        "$effectiveArgs += '--lf'",
        "if ($MaxFail -gt 0)",
        '$effectiveArgs += "--maxfail=$MaxFail"',
        "if ($Parallel)",
        "$effectiveArgs += '-n'",
        "$effectiveArgs += $ParallelWorkers",
        "$effectiveArgs += '--dist'",
        "$effectiveArgs += $ParallelDist",
        "exit $exitCode",
    ]:
        _assert_contains(content, needle)


def test_governance_wrapper_contract() -> None:
    content = _read(GOVERNANCE_WRAPPER_PATH)

    for needle in [
        "[CmdletBinding(PositionalBinding = $false)]",
        "[int]$TimeoutSeconds = 1200",
        "[Parameter(ValueFromRemainingArguments = $true)]",
        "governance_suite.ps1",
        "validation_timeout_guard.ps1",
        "-Label 'governance'",
        "exit $exitCode",
    ]:
        _assert_contains(content, needle)


@pytest.mark.parametrize(
    ("script", "expected_tokens"),
    [
        (LEAN_WRAPPER_PATH, ("lake", "build", "ToeFormal")),
        (PYTEST_WRAPPER_PATH, ("py.ps1", "-m", "pytest", "formal/python/tests", "-q")),
        (GOVERNANCE_WRAPPER_PATH, ("governance_suite.ps1",)),
    ],
)
def test_validation_wrappers_support_dry_run(script: Path, expected_tokens: tuple[str, ...]) -> None:
    shell = shutil.which("pwsh") or shutil.which("powershell") or shutil.which("powershell.exe")
    if shell is None:
        pytest.skip("PowerShell is required for wrapper dry-run validation.")

    completed = subprocess.run(
        [shell, "-NoProfile", "-ExecutionPolicy", "Bypass", "-File", str(script), "-DryRun"],
        cwd=REPO_ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=30,
        check=False,
    )

    assert completed.returncode == 0, completed.stdout
    assert "validation_runner.DRY_RUN" in completed.stdout
    for token in expected_tokens:
        assert token in completed.stdout


def test_pytest_wrapper_forwards_positional_pytest_args() -> None:
    shell = shutil.which("pwsh") or shutil.which("powershell") or shutil.which("powershell.exe")
    if shell is None:
        pytest.skip("PowerShell is required for wrapper dry-run validation.")

    completed = subprocess.run(
        [
            shell,
            "-NoProfile",
            "-ExecutionPolicy",
            "Bypass",
            "-File",
            str(PYTEST_WRAPPER_PATH),
            "-DryRun",
            "formal/python/tests/test_validation_timeout_wrappers_gate.py",
            "-k",
            "dry_run",
        ],
        cwd=REPO_ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=30,
        check=False,
    )

    assert completed.returncode == 0, completed.stdout
    assert "formal/python/tests/test_validation_timeout_wrappers_gate.py" in completed.stdout
    assert "-k dry_run" in completed.stdout


def test_pytest_wrapper_default_dry_run_command_is_unchanged() -> None:
    shell = shutil.which("pwsh") or shutil.which("powershell") or shutil.which("powershell.exe")
    if shell is None:
        pytest.skip("PowerShell is required for wrapper dry-run validation.")

    completed = subprocess.run(
        [
            shell,
            "-NoProfile",
            "-ExecutionPolicy",
            "Bypass",
            "-File",
            str(PYTEST_WRAPPER_PATH),
            "-DryRun",
        ],
        cwd=REPO_ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=30,
        check=False,
    )

    assert completed.returncode == 0, completed.stdout
    assert "-m pytest formal/python/tests -q" in completed.stdout
    assert "-n auto" not in completed.stdout
    assert "--dist loadfile" not in completed.stdout


def test_pytest_wrapper_parallel_dry_run_is_additive() -> None:
    shell = shutil.which("pwsh") or shutil.which("powershell") or shutil.which("powershell.exe")
    if shell is None:
        pytest.skip("PowerShell is required for wrapper dry-run validation.")

    completed = subprocess.run(
        [
            shell,
            "-NoProfile",
            "-ExecutionPolicy",
            "Bypass",
            "-File",
            str(PYTEST_WRAPPER_PATH),
            "-DryRun",
            "-Parallel",
            "-ParallelWorkers",
            "auto",
            "-ParallelDist",
            "loadfile",
        ],
        cwd=REPO_ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=30,
        check=False,
    )

    assert completed.returncode == 0, completed.stdout
    assert "-m pytest formal/python/tests -n auto --dist loadfile -q" in completed.stdout


def test_lean_wrapper_default_dry_run_command_is_unchanged() -> None:
    shell = shutil.which("pwsh") or shutil.which("powershell") or shutil.which("powershell.exe")
    if shell is None:
        pytest.skip("PowerShell is required for wrapper dry-run validation.")

    completed = subprocess.run(
        [
            shell,
            "-NoProfile",
            "-ExecutionPolicy",
            "Bypass",
            "-File",
            str(LEAN_WRAPPER_PATH),
            "-DryRun",
        ],
        cwd=REPO_ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=30,
        check=False,
    )

    assert completed.returncode == 0, completed.stdout
    assert "validation_runner.command lake build ToeFormal" in completed.stdout
    assert "-Kthreads" not in completed.stdout


def test_lean_wrapper_threads_dry_run_is_additive() -> None:
    shell = shutil.which("pwsh") or shutil.which("powershell") or shutil.which("powershell.exe")
    if shell is None:
        pytest.skip("PowerShell is required for wrapper dry-run validation.")

    completed = subprocess.run(
        [
            shell,
            "-NoProfile",
            "-ExecutionPolicy",
            "Bypass",
            "-File",
            str(LEAN_WRAPPER_PATH),
            "-DryRun",
            "-Threads",
            "8",
        ],
        cwd=REPO_ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=30,
        check=False,
    )

    assert completed.returncode == 0, completed.stdout
    assert "validation_runner.command lake -Kthreads=8 build ToeFormal" in completed.stdout
