from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "THEOREM_GAP_SINGLE_ROW_EXECUTION_20260411_v0"

TRANCHE_PATH = REPO_ROOT / "formal" / "docs" / "release" / "THEOREM_GAP_SINGLE_ROW_EXECUTION_TRANCHE_20260411_v0.json"
ROW_TREND_PATH = REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_row_outcome_trend_20260411_v0.json"
TREND_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_trend_window_20260410_v0.json"
LINKAGE_PATH = REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_execution_linkage_20260411_v0.json"
LEDGER_PATH = REPO_ROOT / "formal" / "output" / "reports" / "physics_progress_ledger_v0.json"


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
    tranche = _read_json(TRANCHE_PATH)
    row_trend = _read_json(ROW_TREND_PATH)
    trend = _read_json(TREND_PATH)
    linkage = _read_json(LINKAGE_PATH)
    ledger = _read_json(LEDGER_PATH)

    target_row = str(tranche.get("target_row", "")).strip()
    expected_change = str(tranche.get("expected_blocker_state_change", "")).strip()
    success_threshold = str(tranche.get("success_threshold", "")).strip()
    failure_threshold = str(tranche.get("failure_threshold", "")).strip()

    row_counts = row_trend.get("objective_quality", {}).get("inputs", {}).get("row_outcome_counts", {})
    target_row_counts = row_counts.get(target_row, {}) if isinstance(row_counts, dict) else {}
    row_success_count = int(target_row_counts.get("success", 0) or 0)
    row_no_change_count = int(target_row_counts.get("no_change", 0) or 0)
    row_failure_count = int(target_row_counts.get("failure", 0) or 0)

    theorem_prior = int(trend.get("blocker_counts", {}).get("prior", {}).get("THEOREM_GAP", 0))
    theorem_current = int(trend.get("blocker_counts", {}).get("current", {}).get("THEOREM_GAP", theorem_prior))
    theorem_delta = theorem_current - theorem_prior
    linkage_no_change = int(linkage.get("objective_quality", {}).get("inputs", {}).get("no_change_count", 0) or 0)

    evidence_bundle = tranche.get("required_evidence_bundle", {})
    evidence_exists = True
    for key in (
        "declaration_pointer",
        "execution_checkpoint_pointer",
        "linkage_registry_pointer",
        "row_outcome_trend_pointer",
    ):
        pointer = str(evidence_bundle.get(key, "")).strip()
        if not pointer or not (REPO_ROOT / pointer).exists():
            evidence_exists = False
            break

    no_change_policy = tranche.get("no_change_fail_closed_policy", {})
    no_change_route = str(no_change_policy.get("route_token", "")).strip()
    no_change_route_pointer = str(no_change_policy.get("rework_evidence_pointer", "")).strip()
    no_change_route_exists = bool(no_change_route_pointer) and (REPO_ROOT / no_change_route_pointer).exists()

    criteria = {
        "single_target_row_declared": bool(target_row),
        "single_target_row_has_activity_surface": isinstance(target_row_counts, dict),
        "expected_change_declared": expected_change == "NEGATIVE_THEOREM_GAP_DELTA_REQUIRED",
        "success_failure_thresholds_declared": (
            success_threshold == "THEOREM_GAP_DELTA_LT_0_AND_ROW_SUCCESS_COUNT_GT_0"
            and failure_threshold == "THEOREM_GAP_DELTA_GE_0_OR_ROW_SUCCESS_COUNT_EQ_0"
        ),
        "required_evidence_bundle_exists": evidence_exists,
        "no_change_route_policy_pinned": (
            no_change_policy.get("required") is True
            and no_change_route == "ROUTE_TO_THEOREM_GAP_REWORK"
            and no_change_route_exists
        ),
    }

    success_observed = theorem_delta < 0 and row_success_count > 0
    no_change_observed = theorem_delta == 0 and row_success_count == 0

    objective_criteria = {
        "target_row_success_observed": success_observed,
        "theorem_gap_delta_negative": theorem_delta < 0,
        "target_row_row_success_count_positive": row_success_count > 0,
        "no_change_fail_closed_route_satisfied": (not no_change_observed) or (
            no_change_route == "ROUTE_TO_THEOREM_GAP_REWORK" and no_change_route_exists and linkage_no_change > 0
        ),
        "ledger_progress_classification_true_progress": str(ledger.get("progress_classification", "")) == "PROGRESS",
    }

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": criteria,
        "objective_quality": {
            "criteria": objective_criteria,
            "inputs": {
                "target_row": target_row,
                "target_row_success_count": row_success_count,
                "target_row_failure_count": row_failure_count,
                "target_row_no_change_count": row_no_change_count,
                "theorem_gap_prior": theorem_prior,
                "theorem_gap_current": theorem_current,
                "theorem_gap_delta": theorem_delta,
                "linkage_no_change_count": linkage_no_change,
                "no_change_route_token": no_change_route,
            },
            "summary": {
                "all_criteria_satisfied": all(objective_criteria.values()),
                "phase_status": "COMPLETE" if all(objective_criteria.values()) else "INCOMPLETE",
                "next_action": (
                    "MAINTENANCE_MODE"
                    if all(objective_criteria.values())
                    else "EXECUTE_TARGET_ROW_BLOCKER_MOVING_REWORK"
                ),
            },
        },
        "summary": {
            "all_criteria_satisfied": all(criteria.values()),
            "phase_status": "COMPLETE" if all(criteria.values()) else "INCOMPLETE",
            "next_action": (
                "EXECUTE_TARGET_ROW_BLOCKER_MOVING_REWORK"
                if all(criteria.values())
                else "RESTORE_SINGLE_ROW_TRANCHE_CONTRACT"
            ),
        },
        "source_bundle": {
            "tranche": _ptr(TRANCHE_PATH),
            "row_outcome_trend": _ptr(ROW_TREND_PATH),
            "trend": _ptr(TREND_PATH),
            "linkage": _ptr(LINKAGE_PATH),
            "ledger": _ptr(LEDGER_PATH),
        },
        "non_claim_boundary": "Repository-local single-row theorem-gap execution artifact only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate theorem-gap single-row execution report.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_single_row_execution_20260411_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"theorem_gap_single_row_execution_report: phase_status={payload['summary']['phase_status']} out={out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())