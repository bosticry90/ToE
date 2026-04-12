from __future__ import annotations

import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.runtime_measurement_history import record_runtime_sample


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "DUAL_TRACK_RUNTIME_SNAPSHOT_v0"
RUNTIME_HISTORY_PATH = REPO_ROOT / "formal" / "output" / "reports" / "runtime_measurement_history_20260411_v0.json"


def _resolve_timestamp(captured_at_utc: str | None) -> str:
    if captured_at_utc:
        return captured_at_utc
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def build_snapshot(
    *,
    captured_at_utc: str | None,
    governance_suite_seconds: float,
    branch_health_full_pytest_seconds: float,
    checkpoint_ladder_seconds: float,
    measurement_mode: str,
    governance_suite_command: str,
    branch_health_full_pytest_command: str,
    checkpoint_ladder_command: str,
) -> dict[str, Any]:
    if governance_suite_seconds <= 0 or branch_health_full_pytest_seconds <= 0 or checkpoint_ladder_seconds <= 0:
        raise ValueError("All runtime values must be positive numbers.")

    if measurement_mode not in {"MEASURED", "MANUAL"}:
        raise ValueError("measurement_mode must be MEASURED or MANUAL")

    source_commands = {
        "governance_suite": governance_suite_command,
        "branch_health_full_pytest": branch_health_full_pytest_command,
        "checkpoint_ladder": checkpoint_ladder_command,
    }
    command_sha256 = {
        key: hashlib.sha256(value.encode("utf-8")).hexdigest()
        for key, value in source_commands.items()
    }

    payload = {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _resolve_timestamp(captured_at_utc),
        "measurement_mode": measurement_mode,
        "runtime_seconds": {
            "governance_suite": round(governance_suite_seconds, 3),
            "branch_health_full_pytest": round(branch_health_full_pytest_seconds, 3),
            "checkpoint_ladder": round(checkpoint_ladder_seconds, 3),
        },
        "source_commands": source_commands,
        "command_sha256": command_sha256,
        "non_claim_boundary": "Operational runtime snapshot only; no theorem or closure claim.",
    }

    sample_count, sample_stats = record_runtime_sample(
        history_path=RUNTIME_HISTORY_PATH,
        role="snapshot",
        measurement_mode=measurement_mode,
        runtime_seconds=payload["runtime_seconds"],
        command_sha256=command_sha256,
    )
    payload["sample_count"] = sample_count
    payload["sample_stats"] = sample_stats
    payload["runtime_history_pointer"] = str(RUNTIME_HISTORY_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Capture dual-track current runtime snapshot.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "dual_track_runtime_snapshot_v0.json",
        help="Output runtime snapshot path.",
    )
    parser.add_argument("--captured-at-utc", default=None)
    parser.add_argument("--governance-suite-seconds", type=float, required=True)
    parser.add_argument("--branch-health-full-pytest-seconds", type=float, required=True)
    parser.add_argument("--checkpoint-ladder-seconds", type=float, required=True)
    parser.add_argument(
        "--measurement-mode",
        default="MANUAL",
        choices=["MEASURED", "MANUAL"],
        help="Runtime evidence mode for captured values.",
    )
    parser.add_argument(
        "--governance-suite-command",
        default="pwsh -NoProfile -ExecutionPolicy Bypass -File ./governance_suite.ps1",
    )
    parser.add_argument(
        "--branch-health-full-pytest-command",
        default="./py.ps1 -m pytest formal/python/tests -q",
    )
    parser.add_argument(
        "--checkpoint-ladder-command",
        default="pwsh -NoProfile -ExecutionPolicy Bypass -File ./checkpoint_ladder.ps1",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    out_path = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_snapshot(
        captured_at_utc=ns.captured_at_utc,
        governance_suite_seconds=ns.governance_suite_seconds,
        branch_health_full_pytest_seconds=ns.branch_health_full_pytest_seconds,
        checkpoint_ladder_seconds=ns.checkpoint_ladder_seconds,
        measurement_mode=ns.measurement_mode,
        governance_suite_command=ns.governance_suite_command,
        branch_health_full_pytest_command=ns.branch_health_full_pytest_command,
        checkpoint_ladder_command=ns.checkpoint_ladder_command,
    )
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    runtimes = payload["runtime_seconds"]
    print(
        "dual_track_runtime_snapshot: "
        f"governance_suite={runtimes['governance_suite']} "
        f"branch_health_full_pytest={runtimes['branch_health_full_pytest']} "
        f"checkpoint_ladder={runtimes['checkpoint_ladder']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
