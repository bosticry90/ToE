from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "RUNTIME_MEASUREMENT_INTEGRITY_20260411_v0"
BASELINE_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_runtime_baseline_20260410_v0.json"
SNAPSHOT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "dual_track_runtime_snapshot_v0.json"
CUTOVER_PATH = REPO_ROOT / "formal" / "output" / "reports" / "dual_track_cutover_report_v0.json"
REQUIRED_RUNTIME_KEYS = (
    "governance_suite",
    "checkpoint_ladder",
    "branch_health_full_pytest",
)
OBJECTIVE_MIN_SAMPLE_COUNT = 3
OBJECTIVE_MAX_DRIFT_PERCENT = 25.0


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def build_report(captured_at_utc: str | None) -> dict[str, Any]:
    baseline = _read_json(BASELINE_PATH)
    snapshot = _read_json(SNAPSHOT_PATH)
    cutover = _read_json(CUTOVER_PATH)

    base_mode = baseline.get("measurement_mode")
    snap_mode = snapshot.get("measurement_mode")
    cutover_policy = cutover.get("measurement_policy", {})

    criteria = {
        "baseline_measured": base_mode == "MEASURED",
        "snapshot_measured": snap_mode == "MEASURED",
        "baseline_has_command_hashes": isinstance(baseline.get("command_sha256"), dict) and len(baseline.get("command_sha256", {})) == 3,
        "snapshot_has_command_hashes": isinstance(snapshot.get("command_sha256"), dict) and len(snapshot.get("command_sha256", {})) == 3,
        "cutover_measured_policy_satisfied": cutover_policy.get("measured_mode_required") is True and cutover_policy.get("measured_mode_satisfied") is True,
    }

    base_runtime = baseline.get("runtime_seconds", {})
    snap_runtime = snapshot.get("runtime_seconds", {})
    has_required_runtime_keys = all(
        key in base_runtime and key in snap_runtime
        for key in REQUIRED_RUNTIME_KEYS
    )

    max_runtime_drift_percent = None
    if has_required_runtime_keys:
        drifts: list[float] = []
        for key in REQUIRED_RUNTIME_KEYS:
            base_value = float(base_runtime[key])
            snap_value = float(snap_runtime[key])
            if base_value <= 0:
                continue
            drifts.append(abs((snap_value - base_value) / base_value) * 100.0)
        if drifts:
            max_runtime_drift_percent = max(drifts)

    baseline_sample_count = int(baseline.get("sample_count", 0) or 0)
    snapshot_sample_count = int(snapshot.get("sample_count", 0) or 0)
    baseline_history_ptr = baseline.get("runtime_history_pointer")
    snapshot_history_ptr = snapshot.get("runtime_history_pointer")
    objective_criteria = {
        "sample_count_threshold_satisfied": (
            baseline_sample_count >= OBJECTIVE_MIN_SAMPLE_COUNT
            and snapshot_sample_count >= OBJECTIVE_MIN_SAMPLE_COUNT
        ),
        "command_hash_stability_satisfied": baseline.get("command_sha256") == snapshot.get("command_sha256"),
        "runtime_key_coverage_satisfied": has_required_runtime_keys,
        "runtime_drift_threshold_satisfied": (
            max_runtime_drift_percent is not None
            and max_runtime_drift_percent <= OBJECTIVE_MAX_DRIFT_PERCENT
        ),
        "runtime_history_pointer_consistency_satisfied": (
            isinstance(baseline_history_ptr, str)
            and baseline_history_ptr
            and baseline_history_ptr == snapshot_history_ptr
        ),
    }

    all_satisfied = all(criteria.values())
    objective_all_satisfied = all(objective_criteria.values())
    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": criteria,
        "objective_quality": {
            "criteria": objective_criteria,
            "inputs": {
                "required_runtime_keys": list(REQUIRED_RUNTIME_KEYS),
                "baseline_sample_count": baseline_sample_count,
                "snapshot_sample_count": snapshot_sample_count,
                "baseline_sample_stats": baseline.get("sample_stats", {}),
                "snapshot_sample_stats": snapshot.get("sample_stats", {}),
                "runtime_history_pointer": baseline_history_ptr,
                "minimum_sample_count_required": OBJECTIVE_MIN_SAMPLE_COUNT,
                "maximum_runtime_drift_percent_allowed": OBJECTIVE_MAX_DRIFT_PERCENT,
                "observed_max_runtime_drift_percent": max_runtime_drift_percent,
            },
            "summary": {
                "all_criteria_satisfied": objective_all_satisfied,
                "phase_status": "COMPLETE" if objective_all_satisfied else "INCOMPLETE",
                "next_action": (
                    "PHASE_C_PACKET41_SUCCESSOR_DECISION_ENFORCEMENT"
                    if objective_all_satisfied
                    else "COLLECT_MULTI_SAMPLE_MEASURED_RUNTIME_EVIDENCE"
                ),
            },
        },
        "summary": {
            "all_criteria_satisfied": all_satisfied,
            "phase_status": "COMPLETE" if all_satisfied else "INCOMPLETE",
            "next_action": "PHASE_C_PACKET41_SUCCESSOR_DECISION_ENFORCEMENT" if all_satisfied else "COLLECT_MEASURED_RUNTIME_EVIDENCE",
        },
        "source_bundle": {
            "baseline": _ptr(BASELINE_PATH),
            "snapshot": _ptr(SNAPSHOT_PATH),
            "cutover": _ptr(CUTOVER_PATH),
        },
        "non_claim_boundary": "Repository-local runtime evidence quality artifact; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate runtime measurement integrity report.")
    parser.add_argument("--out", type=Path, default=REPO_ROOT / "formal" / "output" / "reports" / "runtime_measurement_integrity_20260411_v0.json")
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"runtime_measurement_integrity_report: phase_status={payload['summary']['phase_status']} out={out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
