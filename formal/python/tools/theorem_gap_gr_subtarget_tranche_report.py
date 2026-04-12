from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "THEOREM_GAP_GR_SUBTARGET_TRANCHE_20260411_v0"

DEFAULT_TRANCHE_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "THEOREM_GAP_GR_SUBTARGET_TRANCHE_20260411_v0.json"
)
TREND_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_trend_window_20260410_v0.json"
ROW_TREND_PATH = REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_row_outcome_trend_20260411_v0.json"
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


def build_report(captured_at_utc: str | None, tranche_path: Path) -> dict[str, Any]:
    tranche = _read_json(tranche_path)
    trend = _read_json(TREND_PATH)
    row_trend = _read_json(ROW_TREND_PATH)
    ledger = _read_json(LEDGER_PATH)

    tranche_id = str(tranche.get("tranche_id", "")).strip()
    target_row = str(tranche.get("target_row", "")).strip()
    blocker_class = str(tranche.get("blocker_class", "")).strip()
    measurable_success = str(tranche.get("measurable_success_criterion", "")).strip()
    expected_transition = str(tranche.get("expected_blocker_transition", "")).strip()
    failure_diagnosis = str(tranche.get("failure_diagnosis", "")).strip()

    theorem_prior = int(trend.get("blocker_counts", {}).get("prior", {}).get("THEOREM_GAP", 0))
    theorem_current = int(trend.get("blocker_counts", {}).get("current", {}).get("THEOREM_GAP", theorem_prior))
    theorem_delta = theorem_current - theorem_prior

    row_counts = row_trend.get("objective_quality", {}).get("inputs", {}).get("row_outcome_counts", {})
    target_row_counts = row_counts.get(target_row, {}) if isinstance(row_counts, dict) else {}
    target_row_success_count = int(target_row_counts.get("success", 0) or 0)

    target_row_success_incremented = target_row_success_count > 0

    evidence_bundle = tranche.get("required_evidence_bundle", {})
    evidence_pointers = [
        str(evidence_bundle.get("declaration_pointer", "")).strip(),
        str(evidence_bundle.get("linkage_registry_pointer", "")).strip(),
        str(evidence_bundle.get("row_outcome_trend_pointer", "")).strip(),
        str(evidence_bundle.get("trend_pointer", "")).strip(),
        str(evidence_bundle.get("closure_map_pointer", "")).strip(),
    ]
    evidence_bundle_exists = all(pointer and (REPO_ROOT / pointer).exists() for pointer in evidence_pointers)

    fail_closed = tranche.get("fail_closed_route", {})
    fail_closed_route_ok = (
        str(fail_closed.get("route_token", "")) == "ROUTE_TO_THEOREM_GAP_REWORK"
        and bool(str(fail_closed.get("rework_evidence_pointer", "")).strip())
        and (REPO_ROOT / str(fail_closed.get("rework_evidence_pointer", "")).strip()).exists()
    )

    criteria = {
        "tranche_declares_gr_target_and_blocker": target_row == "ROW-PILLAR-GR-001" and blocker_class == "THEOREM_GAP",
        "tranche_declares_subproblem": bool(str(tranche.get("sub_problem", "")).strip()),
        "tranche_declares_measurable_success": measurable_success
        == "THEOREM_GAP_DELTA_LT_0_OR_TARGET_ROW_SUCCESS_COUNT_INCREMENT",
        "tranche_declares_expected_transition": expected_transition
        == "THEOREM_GAP_REDUCED_BY_AT_LEAST_ONE_OR_ROW_SUCCESS_INCREMENTED",
        "evidence_bundle_exists": evidence_bundle_exists,
        "fail_closed_route_pinned": fail_closed_route_ok,
        "failure_diagnosis_declared": bool(failure_diagnosis),
    }

    success_observed = theorem_delta < 0 or target_row_success_incremented

    objective_criteria = {
        "gr_subtarget_success_observed": success_observed,
        "theorem_gap_delta_negative": theorem_delta < 0,
        "target_row_success_count_incremented": target_row_success_incremented,
        "ledger_progress_classification_true_progress": str(ledger.get("progress_classification", "")) == "PROGRESS",
        "no_change_fail_closed_route_satisfied": (success_observed or fail_closed_route_ok),
    }

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": criteria,
        "objective_quality": {
            "criteria": objective_criteria,
            "inputs": {
                "tranche_id": tranche_id,
                "target_row": target_row,
                "theorem_gap_prior": theorem_prior,
                "theorem_gap_current": theorem_current,
                "theorem_gap_delta": theorem_delta,
                "target_row_success_count": target_row_success_count,
                "target_row_success_count_incremented": target_row_success_incremented,
                "failure_diagnosis": failure_diagnosis,
            },
            "summary": {
                "all_criteria_satisfied": all(objective_criteria.values()),
                "phase_status": "COMPLETE" if all(objective_criteria.values()) else "INCOMPLETE",
                "next_action": (
                    "MAINTENANCE_MODE"
                    if all(objective_criteria.values())
                    else "DEFER_OR_RECLASSIFY_GR_NEAR_TERM_BLOCKER_BURN_LANE"
                ),
            },
        },
        "summary": {
            "all_criteria_satisfied": all(criteria.values()),
            "phase_status": "COMPLETE" if all(criteria.values()) else "INCOMPLETE",
            "next_action": (
                "CONTINUE_GR_SUBTARGET_BLOCKER_MOVING_REWORK"
                if all(criteria.values())
                else "RESTORE_GR_TRANCHE_CONTRACT"
            ),
        },
        "source_bundle": {
            "tranche": _ptr(tranche_path),
            "trend": _ptr(TREND_PATH),
            "row_outcome_trend": _ptr(ROW_TREND_PATH),
            "ledger": _ptr(LEDGER_PATH),
        },
        "non_claim_boundary": "Repository-local GR sub-target theorem-gap tranche artifact only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate theorem-gap GR sub-target tranche report.")
    parser.add_argument("--tranche", type=Path, default=DEFAULT_TRANCHE_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_gr_subtarget_tranche_20260411_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    tranche_path = ns.tranche if ns.tranche.is_absolute() else (REPO_ROOT / ns.tranche)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(ns.captured_at_utc, tranche_path=tranche_path)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"theorem_gap_gr_subtarget_tranche_report: phase_status={payload['summary']['phase_status']} out={out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
