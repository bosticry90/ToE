from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "GOVERNANCE_SCALE_OBSERVABILITY_20260411_v0"
BASELINE_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_runtime_baseline_20260410_v0.json"
SNAPSHOT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "dual_track_runtime_snapshot_v0.json"
INVALIDATION_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_invalidation_telemetry_v0.json"
RUNTIME_HISTORY_PATH = REPO_ROOT / "formal" / "output" / "reports" / "runtime_measurement_history_20260411_v0.json"
AUDIT_PACKET_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_audit_packet_20260410_v0.json"
OBJECTIVE_MIN_HISTORY_SAMPLES = 3
OBJECTIVE_MAX_RUNTIME_CV = 0.2


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


def _percentile(values: list[float], pct: float) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    idx = (len(ordered) - 1) * pct
    lower = int(idx)
    upper = min(lower + 1, len(ordered) - 1)
    frac = idx - lower
    value = ordered[lower] * (1 - frac) + ordered[upper] * frac
    return round(value, 3)


def _mean(values: list[float]) -> float | None:
    if not values:
        return None
    return sum(values) / len(values)


def _runtime_lists(samples: list[dict[str, Any]], key: str) -> list[float]:
    values: list[float] = []
    for sample in samples:
        runtime = sample.get("runtime_seconds", {})
        value = runtime.get(key)
        if isinstance(value, (int, float)):
            values.append(float(value))
    return values


def build_report(captured_at_utc: str | None) -> dict[str, Any]:
    baseline = _read_json(BASELINE_PATH)
    snapshot = _read_json(SNAPSHOT_PATH)
    invalidation = _read_json(INVALIDATION_PATH)
    runtime_history = _read_json(RUNTIME_HISTORY_PATH)
    audit_packet = _read_json(AUDIT_PACKET_PATH)

    baseline_samples = [
        s for s in runtime_history.get("samples", {}).get("baseline", [])
        if s.get("measurement_mode") == "MEASURED"
    ]
    snapshot_samples = [
        s for s in runtime_history.get("samples", {}).get("snapshot", [])
        if s.get("measurement_mode") == "MEASURED"
    ]

    metrics = ("governance_suite", "branch_health_full_pytest", "checkpoint_ladder")
    baseline_percentiles: dict[str, dict[str, float | None]] = {}
    snapshot_percentiles: dict[str, dict[str, float | None]] = {}
    runtime_cv: dict[str, float | None] = {}
    for metric in metrics:
        base_values = _runtime_lists(baseline_samples, metric)
        snap_values = _runtime_lists(snapshot_samples, metric)
        baseline_percentiles[metric] = {
            "p50": _percentile(base_values, 0.50),
            "p95": _percentile(base_values, 0.95),
        }
        snapshot_percentiles[metric] = {
            "p50": _percentile(snap_values, 0.50),
            "p95": _percentile(snap_values, 0.95),
        }

        merged = base_values + snap_values
        mean = _mean(merged)
        if mean is None or mean <= 0:
            runtime_cv[metric] = None
        else:
            variance = sum((v - mean) ** 2 for v in merged) / len(merged)
            runtime_cv[metric] = round((variance ** 0.5) / mean, 6)

    budget_policy = audit_packet.get("runtime_baselines", {}).get("budget_policy", {})
    governance_warn = float(budget_policy.get("governance_warn_seconds", 0) or 0)
    governance_hard = float(budget_policy.get("governance_hard_seconds", 0) or 0)
    branch_warn = float(budget_policy.get("branch_health_warn_seconds", 0) or 0)
    branch_hard = float(budget_policy.get("branch_health_hard_seconds", 0) or 0)

    merged_baseline_governance = _runtime_lists(baseline_samples, "governance_suite")
    merged_snapshot_governance = _runtime_lists(snapshot_samples, "governance_suite")
    merged_baseline_branch = _runtime_lists(baseline_samples, "branch_health_full_pytest")
    merged_snapshot_branch = _runtime_lists(snapshot_samples, "branch_health_full_pytest")

    governance_values = merged_baseline_governance + merged_snapshot_governance
    branch_values = merged_baseline_branch + merged_snapshot_branch
    budget_breach_analysis = {
        "governance_warn_breaches": sum(1 for v in governance_values if governance_warn > 0 and v > governance_warn),
        "governance_hard_breaches": sum(1 for v in governance_values if governance_hard > 0 and v > governance_hard),
        "branch_health_warn_breaches": sum(1 for v in branch_values if branch_warn > 0 and v > branch_warn),
        "branch_health_hard_breaches": sum(1 for v in branch_values if branch_hard > 0 and v > branch_hard),
    }

    output_json_count = sum(1 for _ in (REPO_ROOT / "formal" / "output").rglob("*.json"))
    test_file_count = sum(1 for _ in (REPO_ROOT / "formal" / "python" / "tests").rglob("test_*.py"))

    criteria = {
        "runtime_surfaces_present": isinstance(baseline.get("runtime_seconds"), dict) and isinstance(snapshot.get("runtime_seconds"), dict),
        "invalidation_telemetry_present": invalidation.get("schema_id") == "GOVERNANCE_INVALIDATION_TELEMETRY_v0",
        "artifact_growth_observed": output_json_count > 0,
        "test_surface_observed": test_file_count > 0,
    }
    all_satisfied = all(criteria.values())

    invalidation_runs_total = int(invalidation.get("runs_total", 0))
    invalidation_subset_runs = int(invalidation.get("subset_runs", 0))
    invalidation_full_runs = int(invalidation.get("full_runs", 0))
    invalidation_reason_counters = invalidation.get("reason_counters", {})

    objective_criteria = {
        "runtime_history_multi_sample_satisfied": (
            len(baseline_samples) >= OBJECTIVE_MIN_HISTORY_SAMPLES
            and len(snapshot_samples) >= OBJECTIVE_MIN_HISTORY_SAMPLES
        ),
        "percentile_metrics_materialized": all(
            baseline_percentiles[m]["p50"] is not None
            and baseline_percentiles[m]["p95"] is not None
            and snapshot_percentiles[m]["p50"] is not None
            and snapshot_percentiles[m]["p95"] is not None
            for m in metrics
        ),
        "budget_breach_analysis_materialized": all(k in budget_breach_analysis for k in (
            "governance_warn_breaches",
            "governance_hard_breaches",
            "branch_health_warn_breaches",
            "branch_health_hard_breaches",
        )),
        "invalidation_telemetry_quality_satisfied": (
            invalidation_runs_total >= 3
            and invalidation_subset_runs > 0
            and invalidation_full_runs > 0
            and isinstance(invalidation_reason_counters, dict)
            and len(invalidation_reason_counters) > 0
        ),
        "runtime_flake_proxy_within_bound": all(
            runtime_cv[m] is not None and runtime_cv[m] <= OBJECTIVE_MAX_RUNTIME_CV
            for m in metrics
        ),
    }
    objective_all_satisfied = all(objective_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": criteria,
        "objective_quality": {
            "criteria": objective_criteria,
            "inputs": {
                "minimum_history_samples_required": OBJECTIVE_MIN_HISTORY_SAMPLES,
                "maximum_runtime_cv_allowed": OBJECTIVE_MAX_RUNTIME_CV,
                "baseline_measured_sample_count": len(baseline_samples),
                "snapshot_measured_sample_count": len(snapshot_samples),
                "runtime_cv": runtime_cv,
                "budget_policy": {
                    "governance_warn_seconds": governance_warn,
                    "governance_hard_seconds": governance_hard,
                    "branch_health_warn_seconds": branch_warn,
                    "branch_health_hard_seconds": branch_hard,
                },
                "budget_breach_analysis": budget_breach_analysis,
                "invalidation_runs_total": invalidation_runs_total,
                "invalidation_subset_runs": invalidation_subset_runs,
                "invalidation_full_runs": invalidation_full_runs,
            },
            "summary": {
                "all_criteria_satisfied": objective_all_satisfied,
                "phase_status": "COMPLETE" if objective_all_satisfied else "INCOMPLETE",
                "next_action": (
                    "PHASE_F_CROSS_PLATFORM_PARITY"
                    if objective_all_satisfied
                    else "RESTORE_OBSERVABILITY_ANALYTICS_QUALITY"
                ),
            },
        },
        "observability": {
            "runtime_seconds_baseline": baseline.get("runtime_seconds", {}),
            "runtime_seconds_snapshot": snapshot.get("runtime_seconds", {}),
            "invalidation_runs_total": int(invalidation.get("runs_total", 0)),
            "invalidation_subset_runs": int(invalidation.get("subset_runs", 0)),
            "invalidation_last_subset_hit_rate_percent": float(invalidation.get("last_run", {}).get("subset_hit_rate_percent", 0.0)),
            "formal_output_json_count": output_json_count,
            "formal_python_test_file_count": test_file_count,
            "baseline_runtime_percentiles": baseline_percentiles,
            "snapshot_runtime_percentiles": snapshot_percentiles,
            "budget_breach_analysis": budget_breach_analysis,
            "runtime_flake_proxy_cv": runtime_cv,
        },
        "summary": {
            "all_criteria_satisfied": all_satisfied,
            "phase_status": "COMPLETE" if all_satisfied else "INCOMPLETE",
            "next_action": "PHASE_F_CROSS_PLATFORM_PARITY" if all_satisfied else "RESTORE_OBSERVABILITY_INPUTS",
        },
        "source_bundle": {
            "baseline": _ptr(BASELINE_PATH),
            "snapshot": _ptr(SNAPSHOT_PATH),
            "invalidation": _ptr(INVALIDATION_PATH),
            "runtime_history": _ptr(RUNTIME_HISTORY_PATH),
            "audit_packet": _ptr(AUDIT_PACKET_PATH),
        },
        "non_claim_boundary": "Repository-local observability artifact; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate governance scale observability report.")
    parser.add_argument("--out", type=Path, default=REPO_ROOT / "formal" / "output" / "reports" / "governance_scale_observability_20260411_v0.json")
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"governance_scale_observability_report: phase_status={payload['summary']['phase_status']} out={out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
