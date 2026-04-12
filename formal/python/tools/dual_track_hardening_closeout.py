from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "DUAL_TRACK_HARDENING_CLOSEOUT_v0"

LEDGER_PATH = REPO_ROOT / "formal" / "output" / "reports" / "physics_progress_ledger_v0.json"
CUTOVER_PATH = REPO_ROOT / "formal" / "output" / "reports" / "dual_track_cutover_report_v0.json"
INVALIDATION_TELEMETRY_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_invalidation_telemetry_v0.json"
PARALLEL_CAPABILITY_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_parallel_capability_v0.json"

DEFAULT_MAX_ARTIFACT_AGE_SECONDS = 21600
DEFAULT_MIN_INVALIDATION_RUNS = 2
DEFAULT_MIN_SUBSET_HIT_RATE_PERCENT = 1.0


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _timestamp(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _pointer(path: Path) -> str:
    try:
        return str(path.relative_to(REPO_ROOT)).replace("\\", "/")
    except ValueError:
        return str(path).replace("\\", "/")


def _parse_utc(value: str | None) -> datetime | None:
    if not value:
        return None
    try:
        return datetime.strptime(value, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc)
    except ValueError:
        return None


def _is_fresh(timestamp: str | None, *, max_age_seconds: int, now_utc: datetime) -> bool:
    dt = _parse_utc(timestamp)
    if dt is None:
        return False
    age_seconds = (now_utc - dt).total_seconds()
    return 0 <= age_seconds <= max_age_seconds


def build_closeout(
    *,
    captured_at_utc: str | None,
    max_artifact_age_seconds: int,
    min_invalidation_runs: int,
    min_subset_hit_rate_percent: float,
) -> dict[str, Any]:
    ledger = _read_json(LEDGER_PATH)
    cutover = _read_json(CUTOVER_PATH)
    invalidation = _read_json(INVALIDATION_TELEMETRY_PATH)
    parallel = _read_json(PARALLEL_CAPABILITY_PATH)

    now_utc = datetime.now(timezone.utc)

    cutover_policy = cutover.get("measurement_policy", {})
    cutover_readiness = cutover.get("cutover_readiness", {})
    invalidation_runs_total = int(invalidation.get("runs_total", 0))
    invalidation_subset_runs = int(invalidation.get("subset_runs", 0))
    computed_subset_hit_rate = (
        0.0 if invalidation_runs_total == 0 else round((invalidation_subset_runs / invalidation_runs_total) * 100.0, 3)
    )
    observed_subset_hit_rate = float(invalidation.get("last_run", {}).get("subset_hit_rate_percent", computed_subset_hit_rate))

    freshness = {
        "ledger": _is_fresh(ledger.get("captured_at_utc"), max_age_seconds=max_artifact_age_seconds, now_utc=now_utc),
        "cutover": _is_fresh(cutover.get("captured_at_utc"), max_age_seconds=max_artifact_age_seconds, now_utc=now_utc),
        "invalidation": _is_fresh(invalidation.get("captured_at_utc"), max_age_seconds=max_artifact_age_seconds, now_utc=now_utc),
        "parallel": _is_fresh(parallel.get("captured_at_utc"), max_age_seconds=max_artifact_age_seconds, now_utc=now_utc),
    }

    criteria = {
        "ledger_consistency_guard_active": (
            ledger.get("evidence_bundle", {}).get("consistency", {}).get("status") == "CONSISTENT"
            and ledger.get("evidence_bundle", {}).get("consistency", {}).get("rule")
            == "FAIL_CLOSED_ON_TREND_DELTA_AND_TGC93_ROUTE_CONTRADICTION"
        ),
        "cutover_measured_policy_enforced": (
            cutover_policy.get("measured_mode_required") is True
            and cutover_policy.get("measured_mode_satisfied") is True
            and isinstance(cutover_readiness.get("overall_pass"), bool)
        ),
        "invalidation_telemetry_qualified": (
            invalidation.get("schema_id") == "GOVERNANCE_INVALIDATION_TELEMETRY_v0"
            and invalidation_runs_total >= min_invalidation_runs
            and isinstance(invalidation.get("last_run", {}), dict)
            and observed_subset_hit_rate >= min_subset_hit_rate_percent
        ),
        "parallel_capability_qualified": (
            parallel.get("schema_id") == "GOVERNANCE_PARALLEL_CAPABILITY_v0"
            and parallel.get("parallel_requested") is True
            and parallel.get("capability_available") is True
            and parallel.get("parallel_activated") is True
        ),
        "artifact_recency_qualified": all(freshness.values()),
    }

    all_satisfied = all(criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _timestamp(captured_at_utc),
        "criteria": criteria,
        "summary": {
            "all_criteria_satisfied": all_satisfied,
            "closeout_status": "COMPLETE" if all_satisfied else "INCOMPLETE",
            "next_action": "MAINTENANCE_MODE" if all_satisfied else "CONTINUE_HARDENING",
        },
        "qualification_policy": {
            "max_artifact_age_seconds": max_artifact_age_seconds,
            "min_invalidation_runs": min_invalidation_runs,
            "min_subset_hit_rate_percent": min_subset_hit_rate_percent,
            "observed_subset_hit_rate_percent": observed_subset_hit_rate,
            "freshness": freshness,
        },
        "source_bundle": {
            "physics_progress_ledger": _pointer(LEDGER_PATH),
            "dual_track_cutover_report": _pointer(CUTOVER_PATH),
            "governance_invalidation_telemetry": _pointer(INVALIDATION_TELEMETRY_PATH),
            "governance_parallel_capability": _pointer(PARALLEL_CAPABILITY_PATH),
        },
        "non_claim_boundary": "This closeout artifact is a repository-local governance hardening report and does not assert scientific adequacy.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate dual-track hardening closeout report.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "dual_track_hardening_closeout_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    parser.add_argument("--max-artifact-age-seconds", type=int, default=DEFAULT_MAX_ARTIFACT_AGE_SECONDS)
    parser.add_argument("--min-invalidation-runs", type=int, default=DEFAULT_MIN_INVALIDATION_RUNS)
    parser.add_argument("--min-subset-hit-rate-percent", type=float, default=DEFAULT_MIN_SUBSET_HIT_RATE_PERCENT)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    out_path = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_closeout(
        captured_at_utc=ns.captured_at_utc,
        max_artifact_age_seconds=ns.max_artifact_age_seconds,
        min_invalidation_runs=ns.min_invalidation_runs,
        min_subset_hit_rate_percent=ns.min_subset_hit_rate_percent,
    )
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print(
        "dual_track_hardening_closeout: "
        f"status={payload['summary']['closeout_status']} "
        f"out={out_path}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
