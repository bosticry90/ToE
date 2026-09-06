from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Sequence

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
LEAN_PROJECT = REPO_ROOT / "formal" / "toe_formal"

LEAN_SOURCE_OR_BUILD_FAILURE = "LEAN_SOURCE_OR_BUILD_FAILURE"
LEAN_CACHE_BOOTSTRAP_FAILURE = "LEAN_CACHE_BOOTSTRAP_FAILURE"
LEAN_BUILD_TIMEOUT = "LEAN_BUILD_TIMEOUT"
LEAN_TEST_HARNESS_FAILURE = "LEAN_TEST_HARNESS_FAILURE"

LEAN_PYTEST_MODULES = [
    "formal/python/tests/test_lean_build_gate_qft_evol_object_scaffold.py",
    "formal/python/tests/test_lean_build_gate_qft_gauge_object_scaffold.py",
    "formal/python/tests/test_lean_build_gate_qm_full_derivation_scaffold.py",
    "formal/python/tests/test_lean_build_gate_sr_covariance_object_discharge_stub.py",
]


@dataclass(frozen=True)
class BootstrapStep:
    name: str
    command: list[str]
    cwd: Path
    timeout_seconds: int
    failure_class: str


def frozen_bootstrap_steps(
    *,
    python_executable: str,
    jobs: int,
    fetch_cache: bool,
    bootstrap_timeout_seconds: int,
    build_timeout_seconds: int,
    harness_timeout_seconds: int,
) -> list[BootstrapStep]:
    if jobs not in (1, 2):
        raise ValueError("Clean Lean bootstrap permits exactly 1 or 2 build jobs.")
    steps = [
        BootstrapStep(
            "toolchain_identity",
            ["lake", "--version"],
            LEAN_PROJECT,
            bootstrap_timeout_seconds,
            LEAN_CACHE_BOOTSTRAP_FAILURE,
        ),
        BootstrapStep(
            "dependency_environment",
            ["lake", "env", "lean", "--version"],
            LEAN_PROJECT,
            bootstrap_timeout_seconds,
            LEAN_CACHE_BOOTSTRAP_FAILURE,
        ),
    ]
    if fetch_cache:
        steps.append(
            BootstrapStep(
                "mathlib_cache_bootstrap",
                ["lake", "exe", "cache", "get"],
                LEAN_PROJECT,
                build_timeout_seconds,
                LEAN_CACHE_BOOTSTRAP_FAILURE,
            )
        )
    steps.extend(
        [
            BootstrapStep(
                "committed_module_aggregate",
                [
                    python_executable,
                    "-m",
                    "formal.python.tools.generate_lean_all_modules_aggregate",
                    "--check",
                    "--scope",
                    "committed",
                ],
                REPO_ROOT,
                bootstrap_timeout_seconds,
                LEAN_SOURCE_OR_BUILD_FAILURE,
            ),
            BootstrapStep(
                "toe_formal_build",
                [
                    python_executable,
                    "-m",
                    "formal.python.tools.lean_bounded_lake",
                    "--jobs",
                    str(jobs),
                    "--target",
                    "ToeFormal",
                ],
                REPO_ROOT,
                build_timeout_seconds,
                LEAN_SOURCE_OR_BUILD_FAILURE,
            ),
            BootstrapStep(
                "toe_formal_all_build",
                [
                    python_executable,
                    "-m",
                    "formal.python.tools.lean_bounded_lake",
                    "--jobs",
                    str(jobs),
                    "--target",
                    "ToeFormalAll",
                ],
                REPO_ROOT,
                build_timeout_seconds,
                LEAN_SOURCE_OR_BUILD_FAILURE,
            ),
            BootstrapStep(
                "lean_pytest_harness",
                [python_executable, "-m", "pytest", "-q", *LEAN_PYTEST_MODULES],
                REPO_ROOT,
                harness_timeout_seconds,
                LEAN_TEST_HARNESS_FAILURE,
            ),
        ]
    )
    return steps


def run_bootstrap_step(
    step: BootstrapStep,
    *,
    runner: Callable[..., subprocess.CompletedProcess[str]] = subprocess.run,
) -> dict[str, Any]:
    environment = os.environ.copy()
    try:
        completed = runner(
            step.command,
            cwd=str(step.cwd),
            env=environment,
            check=False,
            capture_output=True,
            text=True,
            timeout=step.timeout_seconds,
        )
    except subprocess.TimeoutExpired as exc:
        return {
            "step": step.name,
            "status": "FAILED",
            "failure_class": LEAN_BUILD_TIMEOUT,
            "timeout_seconds": step.timeout_seconds,
            "stdout": exc.stdout or "",
            "stderr": exc.stderr or "",
        }
    except FileNotFoundError as exc:
        return {
            "step": step.name,
            "status": "FAILED",
            "failure_class": LEAN_CACHE_BOOTSTRAP_FAILURE,
            "returncode": None,
            "stdout": "",
            "stderr": str(exc),
        }
    return {
        "step": step.name,
        "status": "PASSED" if completed.returncode == 0 else "FAILED",
        "failure_class": None if completed.returncode == 0 else step.failure_class,
        "returncode": completed.returncode,
        "stdout": completed.stdout,
        "stderr": completed.stderr,
    }


def execute_bootstrap(
    steps: Sequence[BootstrapStep],
    *,
    runner: Callable[..., subprocess.CompletedProcess[str]] = subprocess.run,
) -> dict[str, Any]:
    results: list[dict[str, Any]] = []
    terminal_failure: str | None = None
    for step in steps:
        if terminal_failure is not None:
            results.append(
                {
                    "step": step.name,
                    "status": "NOT_RUN_SECONDARY_CASCADE",
                    "failure_class": "SECONDARY_CASCADE",
                }
            )
            continue
        result = run_bootstrap_step(step, runner=runner)
        results.append(result)
        terminal_failure = result["failure_class"]
    return {
        "schema_id": "LEAN_CLEAN_BOOTSTRAP_RESULT_v0",
        "status": "PASSED" if terminal_failure is None else "FAILED",
        "failure_class": terminal_failure,
        "sequence": [step.name for step in steps],
        "steps": results,
    }


def _exit_code(result: dict[str, Any]) -> int:
    return {
        None: 0,
        LEAN_CACHE_BOOTSTRAP_FAILURE: 81,
        LEAN_SOURCE_OR_BUILD_FAILURE: 82,
        LEAN_BUILD_TIMEOUT: 83,
        LEAN_TEST_HARNESS_FAILURE: 84,
    }[result["failure_class"]]


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Execute the frozen cold-clone Lean bootstrap and distinguish dependency, "
            "source, timeout, and Python harness failures."
        )
    )
    parser.add_argument("--jobs", type=int, choices=(1, 2), default=1)
    parser.add_argument("--skip-cache-fetch", action="store_true")
    parser.add_argument("--bootstrap-timeout-seconds", type=int, default=900)
    parser.add_argument("--build-timeout-seconds", type=int, default=10800)
    parser.add_argument("--harness-timeout-seconds", type=int, default=1800)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    steps = frozen_bootstrap_steps(
        python_executable=sys.executable,
        jobs=args.jobs,
        fetch_cache=not args.skip_cache_fetch,
        bootstrap_timeout_seconds=args.bootstrap_timeout_seconds,
        build_timeout_seconds=args.build_timeout_seconds,
        harness_timeout_seconds=args.harness_timeout_seconds,
    )
    result = execute_bootstrap(steps)
    rendered = json.dumps(result, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8", newline="\n")
    print(rendered, end="")
    return _exit_code(result)


if __name__ == "__main__":
    raise SystemExit(main())
