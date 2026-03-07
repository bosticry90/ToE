from __future__ import annotations

import argparse
import asyncio
import json
import os
import sys
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCHEMA_ID = "TOE_ADJUDICATION_REPORT_SCHEMA_v0"
RUNNER_VERSION = "v0"
DEFAULT_MANIFEST_REL = Path("formal/docs/release/TOE_ASYNC_ORCHESTRATION_MANIFEST_v0.json")
DEFAULT_REPORT_REL = Path("formal/output/reports/toe_orchestration_report_v0.json")


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = _find_repo_root(Path(__file__))


@dataclass(frozen=True)
class CheckSpec:
    check_id: str
    command: list[str]
    timeout_seconds: int = 300
    cwd: str | None = None


@dataclass(frozen=True)
class CheckResult:
    check_id: str
    status: str
    return_code: int
    duration_seconds: float
    command: list[str]
    stdout_tail: list[str]
    stderr_tail: list[str]


def _tail_lines(text: str, max_lines: int = 20) -> list[str]:
    lines = [line.rstrip("\r") for line in text.splitlines()]
    if len(lines) <= max_lines:
        return lines
    return lines[-max_lines:]


def _expand_tokens(parts: list[str], *, repo_root: Path) -> list[str]:
    replacements = {
        "{python}": sys.executable,
        "{repo_root}": str(repo_root),
    }
    expanded: list[str] = []
    for part in parts:
        value = part
        for token, resolved in replacements.items():
            value = value.replace(token, resolved)
        expanded.append(value)
    return expanded


def _load_manifest(path: Path) -> list[CheckSpec]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    raw_checks = payload.get("checks", [])
    if not isinstance(raw_checks, list) or not raw_checks:
        raise ValueError("Manifest must contain a non-empty 'checks' list.")

    checks: list[CheckSpec] = []
    for i, raw in enumerate(raw_checks):
        if not isinstance(raw, dict):
            raise ValueError(f"Manifest check at index {i} must be an object.")
        check_id = str(raw.get("check_id", "")).strip()
        if not check_id:
            raise ValueError(f"Manifest check at index {i} is missing check_id.")

        command = raw.get("command")
        if not isinstance(command, list) or not command or not all(isinstance(p, str) for p in command):
            raise ValueError(f"Manifest check '{check_id}' must define a string-list command.")

        timeout_seconds = int(raw.get("timeout_seconds", 300))
        cwd = raw.get("cwd")
        if cwd is not None and not isinstance(cwd, str):
            raise ValueError(f"Manifest check '{check_id}' has non-string cwd.")

        checks.append(
            CheckSpec(
                check_id=check_id,
                command=_expand_tokens(command, repo_root=REPO_ROOT),
                timeout_seconds=timeout_seconds,
                cwd=cwd,
            )
        )
    return checks


async def _run_one(spec: CheckSpec, *, semaphore: asyncio.Semaphore) -> CheckResult:
    start = time.perf_counter()
    async with semaphore:
        cwd = str(REPO_ROOT) if spec.cwd is None else str((REPO_ROOT / spec.cwd).resolve())
        try:
            proc = await asyncio.create_subprocess_exec(
                *spec.command,
                cwd=cwd,
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE,
            )
        except FileNotFoundError as exc:
            duration = time.perf_counter() - start
            return CheckResult(
                check_id=spec.check_id,
                status="failed",
                return_code=127,
                duration_seconds=duration,
                command=spec.command,
                stdout_tail=[],
                stderr_tail=[f"launcher error: {exc}"],
            )

        timed_out = False
        try:
            stdout_b, stderr_b = await asyncio.wait_for(proc.communicate(), timeout=spec.timeout_seconds)
        except asyncio.TimeoutError:
            timed_out = True
            proc.kill()
            stdout_b, stderr_b = await proc.communicate()

        duration = time.perf_counter() - start
        stdout_text = stdout_b.decode("utf-8", errors="replace")
        stderr_text = stderr_b.decode("utf-8", errors="replace")

        if timed_out:
            status = "timed_out"
            return_code = -1
        elif proc.returncode == 0:
            status = "passed"
            return_code = 0
        else:
            status = "failed"
            return_code = int(proc.returncode)

        return CheckResult(
            check_id=spec.check_id,
            status=status,
            return_code=return_code,
            duration_seconds=duration,
            command=spec.command,
            stdout_tail=_tail_lines(stdout_text),
            stderr_tail=_tail_lines(stderr_text),
        )


async def run_checks(checks: list[CheckSpec], *, max_concurrency: int) -> dict[str, Any]:
    if max_concurrency < 1:
        raise ValueError("max_concurrency must be >= 1")

    sem = asyncio.Semaphore(max_concurrency)
    tasks = [asyncio.create_task(_run_one(spec, semaphore=sem)) for spec in checks]
    results = await asyncio.gather(*tasks)

    checks_run: list[dict[str, Any]] = []
    failures: list[str] = []
    for result in results:
        checks_run.append(
            {
                "check_id": result.check_id,
                "status": result.status,
                "return_code": result.return_code,
                "duration_seconds": round(result.duration_seconds, 6),
                "command": result.command,
                "stdout_tail": result.stdout_tail,
                "stderr_tail": result.stderr_tail,
            }
        )
        if result.status != "passed":
            failures.append(result.check_id)

    report = {
        "schema_id": SCHEMA_ID,
        "generated_at_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "runner_version": RUNNER_VERSION,
        "checks_run": checks_run,
        "failures": failures,
        "uncertainties": [],
        "speculative_flags": [],
        "manual_review_required": [
            "Human review required before changing any canonical governance/adjudication token."
        ],
    }
    return report


def _json_dump(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run manifest checks with asyncio and emit adjudication report JSON.")
    parser.add_argument(
        "--manifest",
        type=Path,
        default=REPO_ROOT / DEFAULT_MANIFEST_REL,
        help="Path to orchestration manifest JSON.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=REPO_ROOT / DEFAULT_REPORT_REL,
        help="Path to write adjudication report JSON.",
    )
    parser.add_argument("--max-concurrency", type=int, default=max(1, (os.cpu_count() or 2) // 2))
    parser.add_argument("--fail-on-check-failure", action="store_true")
    return parser.parse_args(argv)


def _format_summary(report: dict[str, Any]) -> str:
    checks = report["checks_run"]
    total = len(checks)
    failed = len(report["failures"])
    timed_out = sum(1 for c in checks if c["status"] == "timed_out")
    passed = total - failed
    return f"checks={total} passed={passed} failed={failed} timed_out={timed_out}"


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(sys.argv[1:] if argv is None else argv)
    manifest_path = (REPO_ROOT / ns.manifest).resolve() if not ns.manifest.is_absolute() else ns.manifest
    output_path = (REPO_ROOT / ns.output).resolve() if not ns.output.is_absolute() else ns.output

    checks = _load_manifest(manifest_path)
    report = asyncio.run(run_checks(checks, max_concurrency=ns.max_concurrency))
    _json_dump(output_path, report)

    print(_format_summary(report))
    print(f"report_path={output_path}")

    has_failures = bool(report["failures"])
    if has_failures and ns.fail_on_check_failure:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
