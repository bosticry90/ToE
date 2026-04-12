from __future__ import annotations

import argparse
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "GOVERNANCE_PARALLEL_CAPABILITY_v0"


def _timestamp(captured_at_utc: str | None) -> str:
    if captured_at_utc:
        return captured_at_utc
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _run_pyps1(args: list[str]) -> tuple[int, str]:
    proc = subprocess.run(
        ["pwsh", "-NoProfile", "-ExecutionPolicy", "Bypass", "-File", "./py.ps1", *args],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    return proc.returncode, proc.stdout + proc.stderr


def build_probe(*, workers: str, captured_at_utc: str | None) -> dict[str, Any]:
    help_code, help_text = _run_pyps1(["-m", "pytest", "--help"])
    has_n = help_code == 0 and "-n" in help_text

    probe_code = 1
    if has_n:
        probe_code, _ = _run_pyps1(
            [
                "-m",
                "pytest",
                "-n",
                "1",
                "--collect-only",
                "formal/python/tests/test_state_theory_dag.py",
                "-q",
            ]
        )

    capability_available = has_n and probe_code == 0

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _timestamp(captured_at_utc),
        "parallel_requested": True,
        "capability_available": bool(capability_available),
        "parallel_activated": bool(capability_available),
        "workers": workers,
        "rule": "ENABLE_PARALLEL_ONLY_WHEN_CAPABILITY_PROBE_PASSES_ELSE_FALLBACK_TO_SERIAL",
        "probe_details": {
            "help_check_exit_code": help_code,
            "help_has_n_flag": bool(has_n),
            "collect_probe_exit_code": probe_code,
        },
        "non_claim_boundary": "This report is a repository-local execution capability artifact and does not assert scientific adequacy.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Probe and report governance parallel capability.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "governance_parallel_capability_v0.json",
    )
    parser.add_argument("--workers", default="auto")
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    out_path = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_probe(workers=ns.workers, captured_at_utc=ns.captured_at_utc)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print(
        "governance_parallel_capability_probe: "
        f"capability_available={payload['capability_available']} "
        f"out={out_path}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
