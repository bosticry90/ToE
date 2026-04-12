from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_GLOBAL_COMPLETION_BASELINE_20260411_v0"

STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "release" / "TOE_GLOBAL_COMPLETION_MATRIX_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
LEDGER_PATH = REPO_ROOT / "formal" / "output" / "reports" / "physics_progress_ledger_v0.json"
TREND_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_trend_window_20260410_v0.json"
CLOSEOUT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "toe_enforced_execution_closeout_20260411_v0.json"


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
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    matrix_text = _read(MATRIX_PATH)
    inventory_text = _read(INVENTORY_PATH)
    ledger = _read_json(LEDGER_PATH)
    trend = _read_json(TREND_PATH)
    closeout = _read_json(CLOSEOUT_PATH)

    row_count = sum(1 for line in matrix_text.splitlines() if line.startswith("| ROW-"))
    open_proof_debt_count = inventory_text.count("OPEN_PROOF_DEBT")
    bounded_nonclaim_count = inventory_text.count("BOUNDED_NONCLAIM")

    trend_current = trend.get("blocker_counts", {}).get("current", {})
    ledger_counts = ledger.get("blocker_counts", {})

    governance_objective_complete = closeout.get("summary", {}).get("objective_all_phases_complete") is True
    seam_global_complete = "Seam physics complete global: YES" in state_text

    criteria = {
        "governance_objective_complete": governance_objective_complete,
        "state_declares_seam_global_not_complete": "Seam physics complete global: NO" in state_text,
        "ledger_rework_routed": ledger.get("progress_classification") == "REWORK_ROUTED",
        "trend_non_negative_delta": int(trend.get("blocker_counts", {}).get("net_delta", 0)) >= 0,
        "matrix_row_surface_present": row_count >= 11,
        "inventory_open_debt_present": open_proof_debt_count > 0,
    }
    all_satisfied = all(criteria.values())

    objective_criteria = {
        "ledger_trend_blocker_counts_consistent": trend_current == ledger_counts,
        "theorem_gap_positive": int(ledger_counts.get("THEOREM_GAP", 0)) > 0,
        "seam_integration_gap_positive": int(ledger_counts.get("SEAM_INTEGRATION_GAP", 0)) > 0,
        "parity_drift_positive": int(ledger_counts.get("PARITY_DRIFT", 0)) > 0,
        "roadmap_release_gate_truth_pinned": (
            "Release-gate truth policy" in roadmap_text
            and "governance_suite.ps1" in roadmap_text
            and "pytest formal/python/tests" in roadmap_text
        ),
    }
    objective_all_satisfied = all(objective_criteria.values())

    science_global_complete = (
        seam_global_complete
        and ledger.get("progress_classification") == "PROGRESS"
        and int(trend.get("blocker_counts", {}).get("net_delta", 0)) < 0
        and int(ledger_counts.get("THEOREM_GAP", 0)) == 0
        and int(ledger_counts.get("SEAM_INTEGRATION_GAP", 0)) == 0
        and int(ledger_counts.get("PARITY_DRIFT", 0)) == 0
        and open_proof_debt_count == 0
    )

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": criteria,
        "objective_quality": {
            "criteria": objective_criteria,
            "inputs": {
                "matrix_row_count": row_count,
                "open_proof_debt_count": open_proof_debt_count,
                "bounded_nonclaim_count": bounded_nonclaim_count,
                "blocker_counts": ledger_counts,
                "trend_net_delta": int(trend.get("blocker_counts", {}).get("net_delta", 0)),
            },
            "summary": {
                "all_criteria_satisfied": objective_all_satisfied,
                "phase_status": "COMPLETE" if objective_all_satisfied else "INCOMPLETE",
                "next_action": (
                    "R1_THEOREM_GAP_REDUCTION_WAVE"
                    if objective_all_satisfied
                    else "RESTORE_SCIENCE_BASELINE_CONSISTENCY"
                ),
            },
        },
        "completion_assessment": {
            "governance_objective_complete": governance_objective_complete,
            "science_global_complete": science_global_complete,
            "global_objective_complete": governance_objective_complete and science_global_complete,
            "global_next_action": (
                "MAINTENANCE_MODE"
                if governance_objective_complete and science_global_complete
                else "R1_THEOREM_GAP_REDUCTION_WAVE"
            ),
        },
        "summary": {
            "all_criteria_satisfied": all_satisfied,
            "phase_status": "COMPLETE" if all_satisfied else "INCOMPLETE",
            "next_action": (
                "R1_THEOREM_GAP_REDUCTION_WAVE"
                if all_satisfied
                else "RESTORE_BASELINE_SURFACE_PARITY"
            ),
        },
        "source_bundle": {
            "state": _ptr(STATE_PATH),
            "roadmap": _ptr(ROADMAP_PATH),
            "matrix": _ptr(MATRIX_PATH),
            "inventory": _ptr(INVENTORY_PATH),
            "ledger": _ptr(LEDGER_PATH),
            "trend": _ptr(TREND_PATH),
            "closeout": _ptr(CLOSEOUT_PATH),
        },
        "non_claim_boundary": "Repository-local baseline report for science/global completion control; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate science/global completion baseline report.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "science_global_completion_baseline_20260411_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"science_global_completion_baseline_report: phase_status={payload['summary']['phase_status']} out={out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
