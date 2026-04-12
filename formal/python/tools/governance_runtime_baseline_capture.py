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
SCHEMA_ID = "GOVERNANCE_RUNTIME_BASELINE_20260410_v0"
AUDIT_PACKET_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_audit_packet_20260410_v0.json"
RUNTIME_HISTORY_PATH = REPO_ROOT / "formal" / "output" / "reports" / "runtime_measurement_history_20260411_v0.json"


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _float_or_none(value: Any) -> float | None:
    if value is None:
        return None
    if isinstance(value, (int, float)):
        return float(value)
    try:
        return float(value)
    except (TypeError, ValueError):
        return None


def _resolve_runtime_values(
    *,
    governance_suite_seconds: float | None,
    branch_health_full_pytest_seconds: float | None,
    checkpoint_ladder_seconds: float | None,
) -> tuple[float, float, float]:
    seed = _read_json(AUDIT_PACKET_PATH)
    seed_runtime = seed.get("runtime_baselines", {})

    governance_value = governance_suite_seconds
    if governance_value is None:
        governance_value = _float_or_none(seed_runtime.get("governance_suite_seconds_baseline"))

    branch_value = branch_health_full_pytest_seconds
    if branch_value is None:
        branch_value = _float_or_none(
            seed_runtime.get("branch_health_full_pytest_seconds_baseline")
            or seed_runtime.get("branch_health_pytest_seconds_baseline")
        )

    checkpoint_value = checkpoint_ladder_seconds
    if checkpoint_value is None:
        checkpoint_value = _float_or_none(seed_runtime.get("checkpoint_ladder_seconds_baseline"))

    if governance_value is None or governance_value <= 0:
        raise ValueError("Missing governance suite runtime baseline; pass --governance-suite-seconds.")
    if branch_value is None or branch_value <= 0:
        raise ValueError("Missing branch-health full pytest runtime baseline; pass --branch-health-full-pytest-seconds.")
    if checkpoint_value is None or checkpoint_value <= 0:
        raise ValueError("Missing checkpoint ladder runtime baseline; pass --checkpoint-ladder-seconds.")

    return governance_value, branch_value, checkpoint_value


def build_runtime_baseline(
    *,
    output_path: Path,
    captured_at_utc: str | None,
    governance_suite_seconds: float | None,
    branch_health_full_pytest_seconds: float | None,
    checkpoint_ladder_seconds: float | None,
    measurement_mode: str,
    governance_suite_command: str,
    branch_health_full_pytest_command: str,
    checkpoint_ladder_command: str,
) -> dict[str, Any]:
    governance_value, branch_value, checkpoint_value = _resolve_runtime_values(
        governance_suite_seconds=governance_suite_seconds,
        branch_health_full_pytest_seconds=branch_health_full_pytest_seconds,
        checkpoint_ladder_seconds=checkpoint_ladder_seconds,
    )

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

    payload: dict[str, Any] = {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc
        or datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "measurement_mode": measurement_mode,
        "runtime_seconds": {
            "governance_suite": round(governance_value, 3),
            "branch_health_full_pytest": round(branch_value, 3),
            "checkpoint_ladder": round(checkpoint_value, 3),
        },
        "source_commands": source_commands,
        "command_sha256": command_sha256,
        "non_claim_boundary": "Operational timing baseline only; no theorem or closure claim.",
    }

    sample_count, sample_stats = record_runtime_sample(
        history_path=RUNTIME_HISTORY_PATH,
        role="baseline",
        measurement_mode=measurement_mode,
        runtime_seconds=payload["runtime_seconds"],
        command_sha256=command_sha256,
    )
    payload["sample_count"] = sample_count
    payload["sample_stats"] = sample_stats
    payload["runtime_history_pointer"] = str(RUNTIME_HISTORY_PATH.relative_to(REPO_ROOT)).replace("\\", "/")

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Capture governance runtime baseline artifact.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "governance_runtime_baseline_20260410_v0.json",
        help="Output report path.",
    )
    parser.add_argument(
        "--captured-at-utc",
        default=None,
        help="Optional RFC3339 UTC timestamp override.",
    )
    parser.add_argument("--governance-suite-seconds", type=float, default=None)
    parser.add_argument("--branch-health-full-pytest-seconds", type=float, default=None)
    parser.add_argument("--checkpoint-ladder-seconds", type=float, default=None)
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
    output_path = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_runtime_baseline(
        output_path=output_path,
        captured_at_utc=ns.captured_at_utc,
        governance_suite_seconds=ns.governance_suite_seconds,
        branch_health_full_pytest_seconds=ns.branch_health_full_pytest_seconds,
        checkpoint_ladder_seconds=ns.checkpoint_ladder_seconds,
        measurement_mode=ns.measurement_mode,
        governance_suite_command=ns.governance_suite_command,
        branch_health_full_pytest_command=ns.branch_health_full_pytest_command,
        checkpoint_ladder_command=ns.checkpoint_ladder_command,
    )
    runtimes = payload["runtime_seconds"]
    print(
        "governance_runtime_baseline_capture: "
        f"governance_suite={runtimes['governance_suite']} "
        f"branch_health_full_pytest={runtimes['branch_health_full_pytest']} "
        f"checkpoint_ladder={runtimes['checkpoint_ladder']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
