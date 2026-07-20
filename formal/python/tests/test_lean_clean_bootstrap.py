from __future__ import annotations

import subprocess
from pathlib import Path

from formal.python.tools.lean_clean_bootstrap import (
    LEAN_BUILD_TIMEOUT,
    LEAN_CACHE_BOOTSTRAP_FAILURE,
    LEAN_SOURCE_OR_BUILD_FAILURE,
    LEAN_TEST_HARNESS_FAILURE,
    BootstrapStep,
    execute_bootstrap,
    frozen_bootstrap_steps,
)


def test_frozen_bootstrap_sequence_separates_all_validation_layers() -> None:
    steps = frozen_bootstrap_steps(
        python_executable="python",
        jobs=1,
        fetch_cache=True,
        bootstrap_timeout_seconds=900,
        build_timeout_seconds=10800,
        harness_timeout_seconds=1800,
    )
    assert [step.name for step in steps] == [
        "toolchain_identity",
        "dependency_environment",
        "mathlib_cache_bootstrap",
        "committed_module_aggregate",
        "toe_formal_build",
        "toe_formal_all_build",
        "lean_pytest_harness",
    ]
    assert steps[4].timeout_seconds == 10800
    assert steps[5].timeout_seconds == 10800
    assert steps[3].failure_class == LEAN_SOURCE_OR_BUILD_FAILURE
    assert steps[6].failure_class == LEAN_TEST_HARNESS_FAILURE


def test_first_failure_stops_execution_and_marks_secondary_cascades() -> None:
    steps = [
        BootstrapStep("cache", ["cache"], Path.cwd(), 10, LEAN_CACHE_BOOTSTRAP_FAILURE),
        BootstrapStep("build", ["build"], Path.cwd(), 10, LEAN_SOURCE_OR_BUILD_FAILURE),
    ]
    calls: list[list[str]] = []

    def runner(command: list[str], **_: object) -> subprocess.CompletedProcess[str]:
        calls.append(command)
        return subprocess.CompletedProcess(command, 1, "", "cache unavailable")

    result = execute_bootstrap(steps, runner=runner)
    assert result["failure_class"] == LEAN_CACHE_BOOTSTRAP_FAILURE
    assert calls == [["cache"]]
    assert result["steps"][1]["status"] == "NOT_RUN_SECONDARY_CASCADE"


def test_timeout_has_distinct_failure_class() -> None:
    step = BootstrapStep(
        "build", ["build"], Path.cwd(), 10, LEAN_SOURCE_OR_BUILD_FAILURE
    )

    def runner(command: list[str], **_: object) -> subprocess.CompletedProcess[str]:
        raise subprocess.TimeoutExpired(command, timeout=10)

    result = execute_bootstrap([step], runner=runner)
    assert result["failure_class"] == LEAN_BUILD_TIMEOUT
