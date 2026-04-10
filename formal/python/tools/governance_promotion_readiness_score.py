from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "GOVERNANCE_PROMOTION_READINESS_SCORE_20260410_v0"

RUNTIME_BASELINE_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_runtime_baseline_20260410_v0.json"
ARTIFACT_GROWTH_SNAPSHOT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_artifact_growth_snapshot_20260410_v0.json"
BLOCKER_BURN_REVIEW_PATH = REPO_ROOT / "formal" / "output" / "ws10_tgc76_row_promotion_blocker_burn_review_checkpoint_20260408_v0.json"
CLOSURE_OWNER_MAP_PATH = REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_AUDIT_PACKET_CLOSURE_OWNER_MAP_20260410_v0.json"
BLOCKER_CLOSURE_MAP_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_closure_map_20260410_v0.json"


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _resolve_timestamp(captured_at_utc: str | None) -> str:
    if captured_at_utc:
        return captured_at_utc
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ratio(numerator: int, denominator: int) -> float:
    if denominator <= 0:
        return 0.0
    return numerator / denominator


def _runtime_headroom_score(seconds: float, warn_budget_seconds: float) -> float:
    if warn_budget_seconds <= 0:
        return 0.0
    return max(0.0, min(1.0, 1.0 - (seconds / warn_budget_seconds)))


def _status_from_score(score: float) -> str:
    if score >= 85.0:
        return "READY"
    if score >= 65.0:
        return "CONDITIONAL"
    if score >= 45.0:
        return "WATCH"
    return "BLOCKED"


def build_readiness_report(*, output_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    runtime = _read_json(RUNTIME_BASELINE_REPORT_PATH)
    growth = _read_json(ARTIFACT_GROWTH_SNAPSHOT_PATH)
    blocker_review = _read_json(BLOCKER_BURN_REVIEW_PATH)
    owner_map = _read_json(CLOSURE_OWNER_MAP_PATH)
    blocker_map = _read_json(BLOCKER_CLOSURE_MAP_REPORT_PATH)

    runtime_seconds = runtime.get("runtime_seconds", {})
    if not isinstance(runtime_seconds, dict):
        runtime_seconds = {}

    owner_rows = owner_map.get("rows", [])
    if not isinstance(owner_rows, list):
        owner_rows = []
    owner_total = len(owner_rows)

    blocker_rows_total = int(blocker_map.get("rows_total", 0))
    missing_owner_rows = blocker_map.get("missing_owner_rows", [])
    if not isinstance(missing_owner_rows, list):
        missing_owner_rows = []

    blocker_counts_current = blocker_review.get("blocker_counts", {}).get("current", {})
    if not isinstance(blocker_counts_current, dict):
        blocker_counts_current = {}
    unresolved_total = sum(int(v) for v in blocker_counts_current.values() if isinstance(v, int) and v > 0)

    blocker_net_delta_raw = blocker_review.get("blocker_counts", {}).get("net_delta", 0)
    blocker_net_delta = int(blocker_net_delta_raw) if isinstance(blocker_net_delta_raw, int) else 0

    growth_delta = growth.get("delta_vs_baseline", {})
    if not isinstance(growth_delta, dict):
        growth_delta = {}
    delta_output = int(growth_delta.get("json_files_under_formal_output", 0))
    delta_reports = int(growth_delta.get("json_files_under_formal_output_reports", 0))

    owner_coverage_ratio = _ratio(owner_total, blocker_rows_total)
    blocker_map_coverage_ratio = _ratio(blocker_rows_total - len(missing_owner_rows), blocker_rows_total)

    governance_runtime = float(runtime_seconds.get("governance_suite", 0.0) or 0.0)
    branch_runtime = float(runtime_seconds.get("branch_health_full_pytest", 0.0) or 0.0)
    governance_headroom = _runtime_headroom_score(governance_runtime, 300.0)
    branch_headroom = _runtime_headroom_score(branch_runtime, 900.0)
    runtime_health_score = (governance_headroom + branch_headroom) / 2.0

    weighted_growth_delta = max(0, delta_output) + (2 * max(0, delta_reports))
    artifact_growth_score = max(0.0, min(1.0, 1.0 - (weighted_growth_delta / 20.0)))
    blocker_pressure_score = max(0.0, min(1.0, 1.0 - (unresolved_total / 20.0)))

    blocker_delta_bonus = 0.05 if blocker_net_delta < 0 else 0.0

    weighted_score = (
        0.30 * owner_coverage_ratio
        + 0.20 * blocker_map_coverage_ratio
        + 0.20 * runtime_health_score
        + 0.15 * artifact_growth_score
        + 0.15 * blocker_pressure_score
        + blocker_delta_bonus
    )
    readiness_score = round(max(0.0, min(1.0, weighted_score)) * 100.0, 3)
    readiness_status = _status_from_score(readiness_score)

    payload = {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _resolve_timestamp(captured_at_utc),
        "score": {
            "readiness_score_0_to_100": readiness_score,
            "readiness_status": readiness_status,
            "status_rule": "READY>=85; CONDITIONAL>=65; WATCH>=45; else BLOCKED",
        },
        "components": {
            "owner_coverage_ratio": round(owner_coverage_ratio, 6),
            "blocker_map_coverage_ratio": round(blocker_map_coverage_ratio, 6),
            "runtime_health_score": round(runtime_health_score, 6),
            "artifact_growth_score": round(artifact_growth_score, 6),
            "blocker_pressure_score": round(blocker_pressure_score, 6),
            "blocker_delta_bonus": blocker_delta_bonus,
        },
        "raw_inputs": {
            "owner_rows_total": owner_total,
            "blocker_map_rows_total": blocker_rows_total,
            "missing_owner_rows": missing_owner_rows,
            "blocker_counts_current": blocker_counts_current,
            "blocker_net_delta": blocker_net_delta,
            "artifact_growth_delta": {
                "json_files_under_formal_output": delta_output,
                "json_files_under_formal_output_reports": delta_reports,
            },
            "runtime_seconds": {
                "governance_suite": governance_runtime,
                "branch_health_full_pytest": branch_runtime,
            },
        },
        "source_bundle": {
            "runtime_baseline_report": str(RUNTIME_BASELINE_REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "artifact_growth_snapshot_report": str(ARTIFACT_GROWTH_SNAPSHOT_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "blocker_burn_review": str(BLOCKER_BURN_REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "closure_owner_map": str(CLOSURE_OWNER_MAP_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "blocker_closure_map_report": str(BLOCKER_CLOSURE_MAP_REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
        },
        "non_claim_boundary": "This readiness score is a repository-local governance control signal and does not assert scientific adequacy.",
    }

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate promotion-readiness score report from governance control surfaces.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "governance_promotion_readiness_score_20260410_v0.json",
        help="Output path for promotion-readiness score JSON.",
    )
    parser.add_argument(
        "--captured-at-utc",
        default=None,
        help="Optional RFC3339 UTC timestamp override (e.g. 2026-04-10T00:00:00Z).",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    output_path = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_readiness_report(output_path=output_path, captured_at_utc=ns.captured_at_utc)
    print(
        "governance_promotion_readiness_score: "
        f"status={payload['score']['readiness_status']} "
        f"score={payload['score']['readiness_score_0_to_100']} "
        f"out={output_path}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
