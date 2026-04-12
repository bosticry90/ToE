from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "THEOREM_GAP_REDUCTION_WAVE_20260411_v0"

MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "release" / "TOE_GLOBAL_COMPLETION_MATRIX_v0.md"
CLOSURE_MAP_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_closure_map_20260410_v0.json"
TREND_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_trend_window_20260410_v0.json"
LEDGER_PATH = REPO_ROOT / "formal" / "output" / "reports" / "physics_progress_ledger_v0.json"
SCIENCE_BASELINE_PATH = REPO_ROOT / "formal" / "output" / "reports" / "science_global_completion_baseline_20260411_v0.json"


def _read(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


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
    matrix_text = _read(MATRIX_PATH)
    closure_map = _read_json(CLOSURE_MAP_PATH)
    trend = _read_json(TREND_PATH)
    ledger = _read_json(LEDGER_PATH)
    science_baseline = _read_json(SCIENCE_BASELINE_PATH)

    theorem_rows = [
        row for row in closure_map.get("mappings", [])
        if str(row.get("blocker_class", "")) == "THEOREM_GAP"
    ]
    theorem_row_ids = [str(row.get("row_id", "")) for row in theorem_rows]

    rows_with_artifacts = [
        row for row in theorem_rows
        if (REPO_ROOT / str(row.get("required_closure_artifact", ""))).exists()
    ]
    rows_with_gates = [
        row for row in theorem_rows
        if (REPO_ROOT / str(row.get("closure_gate", ""))).exists()
    ]

    current_counts = trend.get("blocker_counts", {}).get("current", {})
    prior_counts = trend.get("blocker_counts", {}).get("prior", {})
    theorem_current = int(current_counts.get("THEOREM_GAP", 0))
    theorem_prior = int(prior_counts.get("THEOREM_GAP", theorem_current))
    theorem_delta = theorem_current - theorem_prior
    net_delta = int(trend.get("blocker_counts", {}).get("net_delta", 0))

    ledger_counts = ledger.get("blocker_counts", {})
    science_next_action = science_baseline.get("completion_assessment", {}).get("global_next_action")

    criteria = {
        "theorem_gap_rows_surface_present": len(theorem_rows) > 0,
        "matrix_contains_theorem_gap_rows": "| ROW-PILLAR-" in matrix_text and "| THEOREM_GAP |" in matrix_text,
        "theorem_row_paths_materialized": len(rows_with_artifacts) == len(theorem_rows) and len(rows_with_gates) == len(theorem_rows),
        "trend_ledger_theorem_count_consistent": int(ledger_counts.get("THEOREM_GAP", -1)) == theorem_current,
        "science_baseline_routes_to_r1": science_next_action == "R1_THEOREM_GAP_REDUCTION_WAVE",
    }

    objective_criteria = {
        "theorem_gap_count_reduced": theorem_current < theorem_prior,
        "theorem_gap_delta_negative": theorem_delta < 0,
        "trend_net_delta_negative": net_delta < 0,
        "ledger_progress_classification_true_progress": ledger.get("progress_classification") == "PROGRESS",
        "theorem_gap_rows_have_artifact_and_gate_coverage": len(rows_with_artifacts) == len(theorem_rows) and len(rows_with_gates) == len(theorem_rows),
    }

    objective_all_satisfied = all(objective_criteria.values())
    all_satisfied = all(criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": criteria,
        "objective_quality": {
            "criteria": objective_criteria,
            "inputs": {
                "theorem_gap_prior": theorem_prior,
                "theorem_gap_current": theorem_current,
                "theorem_gap_delta": theorem_delta,
                "trend_net_delta": net_delta,
                "theorem_gap_row_count": len(theorem_rows),
                "theorem_gap_row_ids": theorem_row_ids,
                "rows_with_artifact_count": len(rows_with_artifacts),
                "rows_with_gate_count": len(rows_with_gates),
            },
            "summary": {
                "all_criteria_satisfied": objective_all_satisfied,
                "phase_status": "COMPLETE" if objective_all_satisfied else "INCOMPLETE",
                "next_action": (
                    "R2_SEAM_INTEGRATION_REDUCTION_WAVE"
                    if objective_all_satisfied
                    else "CONTINUE_R1_THEOREM_GAP_REDUCTION"
                ),
            },
        },
        "summary": {
            "all_criteria_satisfied": all_satisfied,
            "phase_status": "COMPLETE" if all_satisfied else "INCOMPLETE",
            "next_action": (
                "CONTINUE_R1_THEOREM_GAP_REDUCTION"
                if all_satisfied
                else "RESTORE_R1_SURFACE_PARITY"
            ),
        },
        "source_bundle": {
            "matrix": _ptr(MATRIX_PATH),
            "closure_map": _ptr(CLOSURE_MAP_PATH),
            "trend": _ptr(TREND_PATH),
            "ledger": _ptr(LEDGER_PATH),
            "science_baseline": _ptr(SCIENCE_BASELINE_PATH),
        },
        "non_claim_boundary": "Repository-local theorem-gap reduction control artifact only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate theorem-gap reduction wave report.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_reduction_wave_20260411_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"theorem_gap_reduction_wave_report: phase_status={payload['summary']['phase_status']} out={out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())