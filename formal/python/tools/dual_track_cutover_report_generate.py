from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "DUAL_TRACK_CUTOVER_REPORT_v0"

BASELINE_DEFAULT = REPO_ROOT / "formal" / "output" / "reports" / "governance_runtime_baseline_20260410_v0.json"
CURRENT_DEFAULT = REPO_ROOT / "formal" / "output" / "reports" / "dual_track_runtime_snapshot_v0.json"


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _resolve_timestamp(captured_at_utc: str | None) -> str:
    if captured_at_utc:
        return captured_at_utc
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _delta_percent(baseline: float, current: float) -> float:
    return ((current - baseline) / baseline) * 100.0


def _metric_report(name: str, baseline: float, current: float, required_improvement_percent: float) -> dict[str, Any]:
    delta_percent = _delta_percent(baseline, current)
    improvement_percent = -delta_percent
    pass_threshold = improvement_percent >= required_improvement_percent
    return {
        "metric": name,
        "baseline_seconds": round(baseline, 3),
        "current_seconds": round(current, 3),
        "delta_percent": round(delta_percent, 3),
        "improvement_percent": round(improvement_percent, 3),
        "required_improvement_percent": round(required_improvement_percent, 3),
        "threshold_pass": bool(pass_threshold),
    }


def build_report(
    *,
    baseline_path: Path,
    current_path: Path,
    governance_required_improvement: float,
    checkpoint_required_improvement: float,
    captured_at_utc: str | None,
) -> dict[str, Any]:
    baseline = _read_json(baseline_path)
    current = _read_json(current_path)

    baseline_runtime = baseline.get("runtime_seconds", {})
    current_runtime = current.get("runtime_seconds", {})
    baseline_measurement_mode = str(baseline.get("measurement_mode", "UNKNOWN"))
    current_measurement_mode = str(current.get("measurement_mode", "UNKNOWN"))
    measured_mode_required = True
    measured_mode_satisfied = (
        baseline_measurement_mode == "MEASURED"
        and current_measurement_mode == "MEASURED"
    )

    governance = _metric_report(
        "governance_suite",
        float(baseline_runtime["governance_suite"]),
        float(current_runtime["governance_suite"]),
        governance_required_improvement,
    )
    checkpoint = _metric_report(
        "checkpoint_ladder",
        float(baseline_runtime["checkpoint_ladder"]),
        float(current_runtime["checkpoint_ladder"]),
        checkpoint_required_improvement,
    )

    overall_pass = governance["threshold_pass"] and checkpoint["threshold_pass"] and measured_mode_satisfied

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _resolve_timestamp(captured_at_utc),
        "baseline_pointer": str(baseline_path.relative_to(REPO_ROOT)).replace("\\", "/"),
        "current_pointer": str(current_path.relative_to(REPO_ROOT)).replace("\\", "/"),
        "metrics": {
            "governance_suite": governance,
            "checkpoint_ladder": checkpoint,
        },
        "measurement_policy": {
            "measured_mode_required": measured_mode_required,
            "baseline_measurement_mode": baseline_measurement_mode,
            "current_measurement_mode": current_measurement_mode,
            "measured_mode_satisfied": measured_mode_satisfied,
            "rule": "CUTOVER_PASS_REQUIRES_BASELINE_AND_CURRENT_MEASUREMENT_MODE_MEASURED",
        },
        "cutover_readiness": {
            "overall_pass": bool(overall_pass),
            "rule": "BOTH_GOVERNANCE_AND_CHECKPOINT_IMPROVEMENT_THRESHOLDS_PLUS_MEASURED_MODE_REQUIREMENT_MUST_PASS",
        },
        "non_claim_boundary": "Operational cutover report only; no theorem or closure claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate dual-track runtime cutover report.")
    parser.add_argument("--baseline", type=Path, default=BASELINE_DEFAULT)
    parser.add_argument("--current", type=Path, default=CURRENT_DEFAULT)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "dual_track_cutover_report_v0.json",
    )
    parser.add_argument("--governance-required-improvement-percent", type=float, default=10.0)
    parser.add_argument("--checkpoint-required-improvement-percent", type=float, default=10.0)
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    baseline_path = ns.baseline if ns.baseline.is_absolute() else (REPO_ROOT / ns.baseline)
    current_path = ns.current if ns.current.is_absolute() else (REPO_ROOT / ns.current)
    out_path = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_report(
        baseline_path=baseline_path,
        current_path=current_path,
        governance_required_improvement=ns.governance_required_improvement_percent,
        checkpoint_required_improvement=ns.checkpoint_required_improvement_percent,
        captured_at_utc=ns.captured_at_utc,
    )

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print(
        "dual_track_cutover_report_generate: "
        f"overall_pass={payload['cutover_readiness']['overall_pass']} "
        f"out={out_path}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
