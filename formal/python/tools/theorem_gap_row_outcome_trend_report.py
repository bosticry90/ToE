from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "THEOREM_GAP_ROW_OUTCOME_TREND_20260411_v0"

REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "THEOREM_GAP_TRANCHE_LINKAGE_REGISTRY_20260411_v0.json"
CLOSURE_MAP_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_closure_map_20260410_v0.json"


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
    registry = _read_json(REGISTRY_PATH)
    closure_map = _read_json(CLOSURE_MAP_PATH)

    theorem_rows = {
        str(row.get("row_id", ""))
        for row in closure_map.get("mappings", [])
        if str(row.get("blocker_class", "")) == "THEOREM_GAP"
    }
    entries = list(registry.get("entries", []))

    by_row: dict[str, dict[str, int]] = {}
    for row in theorem_rows:
        by_row[row] = {"success": 0, "failure": 0, "no_change": 0, "total": 0}

    unmapped_entry_count = 0
    for entry in entries:
        row = str(entry.get("target_row", "")).strip()
        outcome = str(entry.get("outcome_status", "")).strip()
        if row not in by_row:
            unmapped_entry_count += 1
            continue
        by_row[row]["total"] += 1
        if outcome == "SUCCESS":
            by_row[row]["success"] += 1
        elif outcome == "FAILURE":
            by_row[row]["failure"] += 1
        elif outcome == "NO_CHANGE":
            by_row[row]["no_change"] += 1

    stagnation_rows = [
        row for row, stats in sorted(by_row.items())
        if stats["total"] > 0 and stats["success"] == 0
    ]
    rows_with_success = [
        row for row, stats in sorted(by_row.items())
        if stats["success"] > 0
    ]

    criteria = {
        "registry_entries_present": len(entries) > 0,
        "row_surface_present": len(theorem_rows) > 0,
        "row_mapping_complete": unmapped_entry_count == 0,
        "row_outcome_aggregation_materialized": all(
            set(stats.keys()) == {"success", "failure", "no_change", "total"}
            for stats in by_row.values()
        ),
    }

    objective_criteria = {
        "at_least_one_row_has_success": len(rows_with_success) > 0,
        "stagnation_rows_empty": len(stagnation_rows) == 0,
        "all_rows_have_activity": all(stats["total"] > 0 for stats in by_row.values()),
    }

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": criteria,
        "objective_quality": {
            "criteria": objective_criteria,
            "inputs": {
                "row_count": len(theorem_rows),
                "registry_entry_count": len(entries),
                "rows_with_success": rows_with_success,
                "stagnation_rows": stagnation_rows,
                "row_outcome_counts": by_row,
                "unmapped_entry_count": unmapped_entry_count,
            },
            "summary": {
                "all_criteria_satisfied": all(objective_criteria.values()),
                "phase_status": "COMPLETE" if all(objective_criteria.values()) else "INCOMPLETE",
                "next_action": (
                    "MAINTENANCE_MODE"
                    if all(objective_criteria.values())
                    else "EXECUTE_ROW_LEVEL_BLOCKER_MOVING_TRANCHE"
                ),
            },
        },
        "summary": {
            "all_criteria_satisfied": all(criteria.values()),
            "phase_status": "COMPLETE" if all(criteria.values()) else "INCOMPLETE",
            "next_action": (
                "MONITOR_ROW_OUTCOME_TRENDS"
                if all(criteria.values())
                else "RESTORE_ROW_OUTCOME_TREND_SURFACE"
            ),
        },
        "source_bundle": {
            "registry": _ptr(REGISTRY_PATH),
            "closure_map": _ptr(CLOSURE_MAP_PATH),
        },
        "non_claim_boundary": "Repository-local theorem-gap row outcome trend artifact only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate theorem-gap row outcome trend report.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_row_outcome_trend_20260411_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"theorem_gap_row_outcome_trend_report: phase_status={payload['summary']['phase_status']} out={out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())