from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "THEOREM_GAP_QM_BOUNDED_STOP_RULE_DECISION_20260411_v0"

QM_SUBTARGET_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_qm_subtarget_tranche_20260411_v0.json"
)
SINGLE_ROW_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_single_row_execution_20260411_v0.json"
)
ROW_TREND_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_row_outcome_trend_20260411_v0.json"
)
TREND_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_trend_window_20260410_v0.json"
)
LINKAGE_REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "THEOREM_GAP_TRANCHE_LINKAGE_REGISTRY_20260411_v0.json"
)

TARGET_ROW = "ROW-PILLAR-QM-001"
NEXT_NARROW_QM_SUBPROBLEM = "QM_PACKET04_THRESHOLD_ALIGNMENT_SUBPROBLEM_v1_NARROW"
MAX_NO_CHANGE_ATTEMPTS = 4


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


def _qm_attempts_for_target_row(linkage_registry: dict[str, Any]) -> list[dict[str, Any]]:
    entries = list(linkage_registry.get("entries", []))
    out: list[dict[str, Any]] = []
    for entry in entries:
        if str(entry.get("target_row", "")) != TARGET_ROW:
            continue
        tranche_id = str(entry.get("tranche_id", ""))
        # Keep bounded rows that actually represent current theorem-gap execution wave attempts.
        if tranche_id.startswith("R") or tranche_id.startswith("TGC-"):
            out.append(entry)
    return out


def _latest_no_change_streak(attempts: list[dict[str, Any]]) -> int:
    streak = 0
    for entry in reversed(attempts):
        if str(entry.get("outcome_status", "")) == "NO_CHANGE":
            streak += 1
        else:
            break
    return streak


def build_report(
    captured_at_utc: str | None,
    qm_subtarget_report_path: Path,
    max_no_change_attempts: int,
    current_no_change_streak: int | None,
    consume_attempt: bool,
) -> dict[str, Any]:
    qm_subtarget = _read_json(qm_subtarget_report_path)
    single_row = _read_json(SINGLE_ROW_REPORT_PATH)
    row_trend = _read_json(ROW_TREND_REPORT_PATH)
    trend = _read_json(TREND_REPORT_PATH)
    linkage = _read_json(LINKAGE_REGISTRY_PATH)

    qm_inputs = qm_subtarget.get("objective_quality", {}).get("inputs", {})
    qm_criteria = qm_subtarget.get("objective_quality", {}).get("criteria", {})
    single_inputs = single_row.get("objective_quality", {}).get("inputs", {})

    theorem_gap_delta = int(qm_inputs.get("theorem_gap_delta", 0) or 0)
    target_row_success_incremented = bool(qm_criteria.get("target_row_success_count_incremented", False))
    target_row_success_count = int(single_inputs.get("target_row_success_count", 0) or 0)

    attempts = _qm_attempts_for_target_row(linkage)
    derived_no_change_streak = _latest_no_change_streak(attempts)
    no_change_streak = (
        derived_no_change_streak
        if current_no_change_streak is None
        else max(0, int(current_no_change_streak))
    )
    theorem_gap_current = int(trend.get("blocker_counts", {}).get("current", {}).get("THEOREM_GAP", 0) or 0)

    movement_observed = theorem_gap_delta < 0 or target_row_success_incremented
    continuation_earned = movement_observed
    effective_no_change_streak = no_change_streak + (1 if consume_attempt and (not movement_observed) else 0)
    stop_rule_triggered = (not movement_observed) and (effective_no_change_streak >= max_no_change_attempts)

    if stop_rule_triggered:
        decision = "DEFER_OR_RECLASSIFY_QM_NEAR_TERM_BLOCKER_BURN_LANE"
        next_action = "SELECT_NON_QM_BLOCKER_BEARING_ROW_FOR_NEXT_ACTIVE_TRANCHE"
        selected_subproblem = None
    else:
        decision = "CONTINUE_QM_ON_NARROWER_SUBPROBLEM"
        next_action = "RUN_QM_NARROW_SUBPROBLEM_BLOCKER_MOVING_TRANCHE"
        selected_subproblem = NEXT_NARROW_QM_SUBPROBLEM

    criteria = {
        "qm_target_row_active": TARGET_ROW in row_trend.get("objective_quality", {}).get("inputs", {}).get("row_outcome_counts", {}),
        "bounded_stop_rule_configured": True,
        "movement_signal_is_measurable": True,
        "failure_route_is_fail_closed": True,
        "attempt_window_materialized": len(attempts) > 0,
    }

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "target": "QM_ACTIVE_LANE_PROBATION_AND_BOUNDED_STOP_RULE",
        "criteria": criteria,
        "inputs": {
            "target_row": TARGET_ROW,
            "theorem_gap_current": theorem_gap_current,
            "theorem_gap_delta": theorem_gap_delta,
            "target_row_success_count": target_row_success_count,
            "target_row_success_count_incremented": target_row_success_incremented,
            "qm_attempt_count_for_row": len(attempts),
            "latest_no_change_streak": no_change_streak,
            "effective_no_change_streak": effective_no_change_streak,
            "max_no_change_attempts": max_no_change_attempts,
            "consume_attempt": consume_attempt,
            "movement_observed": movement_observed,
        },
        "summary": {
            "qm_continuation_earned": continuation_earned,
            "decision": decision,
            "selected_narrow_subproblem": selected_subproblem,
            "next_action": next_action,
            "stop_rule_triggered": stop_rule_triggered,
            "failure_diagnosis": (
                "NO_THEOREM_GAP_DELTA_CHANGE_AND_NO_ROW_SUCCESS_INCREMENT"
                if not movement_observed
                else None
            ),
        },
        "source_bundle": {
            "qm_subtarget_report": _ptr(qm_subtarget_report_path),
            "single_row_report": _ptr(SINGLE_ROW_REPORT_PATH),
            "row_outcome_trend_report": _ptr(ROW_TREND_REPORT_PATH),
            "trend_report": _ptr(TREND_REPORT_PATH),
            "linkage_registry": _ptr(LINKAGE_REGISTRY_PATH),
        },
        "non_claim_boundary": "Repository-local QM bounded stop-rule decision artifact; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate theorem-gap QM bounded stop-rule decision report.")
    parser.add_argument(
        "--qm-subtarget-report-path",
        type=Path,
        default=QM_SUBTARGET_REPORT_PATH,
        help="Path to the current QM subtarget tranche report.",
    )
    parser.add_argument(
        "--max-no-change-attempts",
        type=int,
        default=MAX_NO_CHANGE_ATTEMPTS,
    )
    parser.add_argument(
        "--current-no-change-streak",
        type=int,
        default=None,
        help="Optional override for current no-change streak before this attempt.",
    )
    parser.add_argument(
        "--consume-attempt",
        action="store_true",
        help="Count the current report as one additional attempt when movement is not observed.",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_qm_bounded_stop_rule_decision_20260411_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    qm_subtarget_report_path = (
        ns.qm_subtarget_report_path
        if ns.qm_subtarget_report_path.is_absolute()
        else (REPO_ROOT / ns.qm_subtarget_report_path)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(
        ns.captured_at_utc,
        qm_subtarget_report_path=qm_subtarget_report_path,
        max_no_change_attempts=int(ns.max_no_change_attempts),
        current_no_change_streak=ns.current_no_change_streak,
        consume_attempt=bool(ns.consume_attempt),
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "theorem_gap_qm_bounded_stop_rule_decision_report: "
        f"decision={payload['summary']['decision']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
