from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "THEOREM_GAP_EXECUTION_LINKAGE_20260411_v0"

REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "THEOREM_GAP_TRANCHE_LINKAGE_REGISTRY_20260411_v0.json"
CLOSURE_MAP_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_closure_map_20260410_v0.json"
TREND_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_trend_window_20260410_v0.json"
LEDGER_PATH = REPO_ROOT / "formal" / "output" / "reports" / "physics_progress_ledger_v0.json"

ALLOWED_EXPECTED_CHANGE = {"NEGATIVE_THEOREM_GAP_DELTA_REQUIRED"}
ALLOWED_SUCCESS_THRESHOLD = {"THEOREM_GAP_DELTA_LT_0"}
ALLOWED_ACTUAL_CHANGE = {
    "NEGATIVE_THEOREM_GAP_DELTA_OBSERVED",
    "NO_CHANGE_OBSERVED",
    "POSITIVE_THEOREM_GAP_DELTA_OBSERVED",
}
ALLOWED_OUTCOME_STATUS = {"SUCCESS", "FAILURE", "NO_CHANGE"}
ALLOWED_NO_CHANGE_REWORK_ROUTE = {"ROUTE_TO_THEOREM_GAP_REWORK"}


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
    trend = _read_json(TREND_PATH)
    ledger = _read_json(LEDGER_PATH)

    entries = list(registry.get("entries", []))
    theorem_rows = {
        str(row.get("row_id", ""))
        for row in closure_map.get("mappings", [])
        if str(row.get("blocker_class", "")) == "THEOREM_GAP"
    }

    coverage_rows: set[str] = set()
    missing_fields_count = 0
    missing_file_pointers_count = 0
    invalid_enum_count = 0
    mismatched_target_row_count = 0
    duplicate_tranche_id_count = 0
    duplicate_target_row_per_tranche_count = 0
    invalid_no_change_rework_routing_count = 0

    tranche_to_row: dict[str, str] = {}

    success_count = 0
    failure_count = 0
    no_change_count = 0

    for entry in entries:
        tranche_id = str(entry.get("tranche_id", "")).strip()
        target_row = str(entry.get("target_row", "")).strip()
        expected = str(entry.get("expected_blocker_state_change", "")).strip()
        success_threshold = str(entry.get("success_threshold", "")).strip()
        actual = str(entry.get("actual_blocker_state_change", "")).strip()
        outcome = str(entry.get("outcome_status", "")).strip()
        no_change_rework_route = str(entry.get("no_change_rework_route", "")).strip()
        rework_evidence_pointer = str(entry.get("rework_evidence_pointer", "")).strip()
        declaration_pointer = str(entry.get("declaration_pointer", "")).strip()
        evidence_pointer = str(entry.get("evidence_pointer", "")).strip()

        required_values = [
            tranche_id,
            target_row,
            expected,
            success_threshold,
            actual,
            outcome,
            declaration_pointer,
            evidence_pointer,
        ]
        if any(not value for value in required_values):
            missing_fields_count += 1

        if (
            expected not in ALLOWED_EXPECTED_CHANGE
            or success_threshold not in ALLOWED_SUCCESS_THRESHOLD
            or actual not in ALLOWED_ACTUAL_CHANGE
            or outcome not in ALLOWED_OUTCOME_STATUS
        ):
            invalid_enum_count += 1

        if tranche_id in tranche_to_row:
            duplicate_tranche_id_count += 1
            if tranche_to_row[tranche_id] != target_row:
                duplicate_target_row_per_tranche_count += 1
        else:
            tranche_to_row[tranche_id] = target_row

        if target_row not in theorem_rows:
            mismatched_target_row_count += 1
        else:
            coverage_rows.add(target_row)

        for pointer in (declaration_pointer, evidence_pointer, rework_evidence_pointer):
            if pointer and not (REPO_ROOT / pointer).exists():
                missing_file_pointers_count += 1

        if outcome == "NO_CHANGE":
            if (
                no_change_rework_route not in ALLOWED_NO_CHANGE_REWORK_ROUTE
                or not rework_evidence_pointer
            ):
                invalid_no_change_rework_routing_count += 1

        if outcome == "SUCCESS":
            success_count += 1
        elif outcome == "FAILURE":
            failure_count += 1
        elif outcome == "NO_CHANGE":
            no_change_count += 1

    theorem_prior = int(trend.get("blocker_counts", {}).get("prior", {}).get("THEOREM_GAP", 0))
    theorem_current = int(trend.get("blocker_counts", {}).get("current", {}).get("THEOREM_GAP", theorem_prior))
    theorem_delta = theorem_current - theorem_prior
    net_delta = int(trend.get("blocker_counts", {}).get("net_delta", 0))

    criteria = {
        "registry_entries_present": len(entries) > 0,
        "required_linkage_fields_complete": missing_fields_count == 0,
        "linkage_enum_values_valid": invalid_enum_count == 0,
        "single_target_row_per_tranche_enforced": (
            duplicate_tranche_id_count == 0 and duplicate_target_row_per_tranche_count == 0
        ),
        "no_change_requires_rework_route": invalid_no_change_rework_routing_count == 0,
        "target_rows_exist_in_theorem_gap_surface": mismatched_target_row_count == 0,
        "declaration_and_evidence_pointers_exist": missing_file_pointers_count == 0,
    }

    objective_criteria = {
        "at_least_one_tranche_success_recorded": success_count > 0,
        "theorem_gap_count_reduced": theorem_current < theorem_prior,
        "theorem_gap_delta_negative": theorem_delta < 0,
        "trend_net_delta_negative": net_delta < 0,
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
                "registry_entry_count": len(entries),
                "distinct_tranche_count": len(tranche_to_row),
                "theorem_gap_row_count": len(theorem_rows),
                "covered_theorem_gap_rows": sorted(coverage_rows),
                "covered_theorem_gap_row_count": len(coverage_rows),
                "duplicate_tranche_id_count": duplicate_tranche_id_count,
                "duplicate_target_row_per_tranche_count": duplicate_target_row_per_tranche_count,
                "invalid_no_change_rework_routing_count": invalid_no_change_rework_routing_count,
                "success_count": success_count,
                "failure_count": failure_count,
                "no_change_count": no_change_count,
                "theorem_gap_prior": theorem_prior,
                "theorem_gap_current": theorem_current,
                "theorem_gap_delta": theorem_delta,
                "trend_net_delta": net_delta,
            },
            "summary": {
                "all_criteria_satisfied": all(objective_criteria.values()),
                "phase_status": "COMPLETE" if all(objective_criteria.values()) else "INCOMPLETE",
                "next_action": (
                    "R3_GLOBAL_OBJECTIVE_CLOSEOUT_WAVE"
                    if all(objective_criteria.values())
                    else "CONTINUE_R2_BLOCKER_MOVING_EXECUTION_LINKAGE"
                ),
            },
        },
        "summary": {
            "all_criteria_satisfied": all(criteria.values()),
            "phase_status": "COMPLETE" if all(criteria.values()) else "INCOMPLETE",
            "next_action": (
                "CONTINUE_R2_BLOCKER_MOVING_EXECUTION_LINKAGE"
                if all(criteria.values())
                else "RESTORE_R2_LINKAGE_CONTRACT"
            ),
        },
        "source_bundle": {
            "registry": _ptr(REGISTRY_PATH),
            "closure_map": _ptr(CLOSURE_MAP_PATH),
            "trend": _ptr(TREND_PATH),
            "ledger": _ptr(LEDGER_PATH),
        },
        "non_claim_boundary": "Repository-local theorem-gap execution linkage artifact only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate theorem-gap execution linkage report.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_execution_linkage_20260411_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"theorem_gap_execution_linkage_report: phase_status={payload['summary']['phase_status']} out={out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())