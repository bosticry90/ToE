from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "GR_BLOCKER_MOVING_TRANCHE_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "GR_BLOCKER_MOVING_TRANCHE_20260412_v0.json"
)


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


def _execution_valid(checkpoint: dict[str, Any]) -> bool:
    evidence = dict(checkpoint.get("evidence", {}))
    failed = evidence.get("failed", 1)
    passed = evidence.get("passed", 0)
    return (
        int(1 if failed is None else failed) == 0
        and int(0 if passed is None else passed) > 0
        and not bool(checkpoint.get("packet05_matrix_drift_detected", True))
        and not bool(checkpoint.get("seam_coupling_regression_detected", True))
    )


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    movement_policy = dict(declaration.get("movement_policy", {}))
    contract = dict(declaration.get("classification_contract", {}))

    rebalance_path = REPO_ROOT / str(required_inputs.get("science_rebalance_report", "")).strip()
    checkpoint_path = REPO_ROOT / str(required_inputs.get("execution_checkpoint", "")).strip()
    subtarget_path = REPO_ROOT / str(required_inputs.get("gr_subtarget_report", "")).strip()
    stop_rule_path = REPO_ROOT / str(required_inputs.get("gr_stop_rule_decision_report", "")).strip()
    trend_path = REPO_ROOT / str(required_inputs.get("trend_report", "")).strip()
    row_trend_path = REPO_ROOT / str(required_inputs.get("row_outcome_trend_report", "")).strip()
    ledger_path = REPO_ROOT / str(required_inputs.get("ledger_report", "")).strip()

    rebalance = _read_json(rebalance_path)
    checkpoint = _read_json(checkpoint_path)
    subtarget = _read_json(subtarget_path)
    stop_rule = _read_json(stop_rule_path)
    trend = _read_json(trend_path)
    row_trend = _read_json(row_trend_path)
    ledger = _read_json(ledger_path)

    target_row = str(declaration.get("target_row", "")).strip()
    expected_rebalance_outcome = "ACTIVATE_GR_BLOCKER_MOVING_TRANCHE"
    rebalance_outcome = str(dict(rebalance.get("summary", {})).get("selected_outcome", "")).strip()

    execution_valid = _execution_valid(checkpoint)
    subtarget_target_row = str(dict(subtarget.get("objective_quality", {}).get("inputs", {})).get("target_row", "")).strip()

    theorem_gap_prior = int(trend.get("blocker_counts", {}).get("prior", {}).get("THEOREM_GAP", 0) or 0)
    theorem_gap_current = int(trend.get("blocker_counts", {}).get("current", {}).get("THEOREM_GAP", theorem_gap_prior) or 0)
    theorem_gap_delta = theorem_gap_current - theorem_gap_prior

    row_counts = dict(dict(row_trend.get("objective_quality", {}).get("inputs", {})).get("row_outcome_counts", {})).get(
        target_row, {}
    )
    target_row_success_increment_gt_0 = int(row_counts.get("success", 0) or 0) > 0

    blocker_state_change = str(ledger.get("actual_blocker_state_change", "")).strip()
    blocker_state_token_changed = blocker_state_change not in {"", "NO_DELTA_DETECTED_ROUTE_TO_REWORK"}

    stop_summary = dict(stop_rule.get("summary", {}))
    stop_rule_triggered = bool(stop_summary.get("stop_rule_triggered", False))
    stop_decision = str(stop_summary.get("decision", "")).strip()
    different_attack_class = stop_rule_triggered and stop_decision == "DEFER_OR_RECLASSIFY_GR_NEAR_TERM_BLOCKER_BURN_LANE"

    theorem_gap_delta_lt_0 = theorem_gap_delta < 0
    all_movement_signals_false = not any(
        [theorem_gap_delta_lt_0, target_row_success_increment_gt_0, blocker_state_token_changed]
    )

    scope_valid = subtarget_target_row == target_row
    preconditions_ok = rebalance_outcome == expected_rebalance_outcome and execution_valid and scope_valid

    if preconditions_ok and (theorem_gap_delta_lt_0 or target_row_success_increment_gt_0 or blocker_state_token_changed):
        classification = "GR_BLOCKER_MOVED"
        next_action = "CONTINUE_GR_BLOCKER_MOVING_PROGRAM"
    elif preconditions_ok and different_attack_class:
        classification = "GR_REQUIRES_DIFFERENT_ATTACK_CLASS"
        next_action = "SELECT_NEXT_ATTACK_CLASS_FOR_GR_BLOCKER_ROW"
    elif preconditions_ok and all_movement_signals_false:
        classification = "GR_VALID_BUT_NONMOVING"
        next_action = "ISSUE_GR_NONMOVING_RULING_AND_HOLD_LOOP"
    else:
        classification = "GR_PATH_FALSIFIED"
        next_action = "STOP_GR_PATH_AND_REVIEW_PRECONDITIONS_OR_SCOPE"

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    if classification not in allowed_outcomes:
        classification = str(contract.get("default_outcome", "GR_VALID_BUT_NONMOVING")).strip()

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "rebalance_selected_gr_lane": rebalance_outcome == expected_rebalance_outcome,
            "execution_checkpoint_valid": execution_valid,
            "subtarget_scope_matches_target_row": scope_valid,
            "single_terminal_outcome_rule_declared": str(contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_GR_BLOCKER_OUTCOME",
            "no_loop_rule_declared": str(movement_policy.get("no_loop_rule", "")).strip()
            == "ONE_BOUNDED_EXECUTION_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "theorem_gap_delta_lt_0": theorem_gap_delta_lt_0,
                "target_row_success_increment_gt_0": target_row_success_increment_gt_0,
                "blocker_state_token_changed": blocker_state_token_changed,
                "different_attack_class_triggered": different_attack_class,
                "all_movement_signals_false": all_movement_signals_false,
                "classification_materialized": classification in allowed_outcomes,
            },
            "inputs": {
                "rebalance_outcome": rebalance_outcome,
                "target_row": target_row,
                "subtarget_target_row": subtarget_target_row,
                "theorem_gap_prior": theorem_gap_prior,
                "theorem_gap_current": theorem_gap_current,
                "theorem_gap_delta": theorem_gap_delta,
                "row_success_count": int(row_counts.get("success", 0) or 0),
                "blocker_state_change": blocker_state_change,
                "stop_rule_triggered": stop_rule_triggered,
                "stop_decision": stop_decision,
                "success_rule": movement_policy.get("success_rule"),
                "nonmoving_rule": movement_policy.get("nonmoving_rule"),
                "different_attack_class_rule": movement_policy.get("different_attack_class_rule"),
                "falsification_rule": movement_policy.get("falsification_rule"),
            },
            "summary": {
                "all_criteria_satisfied": classification
                in {"GR_BLOCKER_MOVED", "GR_VALID_BUT_NONMOVING", "GR_REQUIRES_DIFFERENT_ATTACK_CLASS"},
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "tranche_classification": classification,
            "target_row": target_row,
            "theorem_gap_delta": theorem_gap_delta,
            "target_row_success_increment_gt_0": target_row_success_increment_gt_0,
            "blocker_state_token_changed": blocker_state_token_changed,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_rebalance_report": _ptr(rebalance_path),
            "execution_checkpoint": _ptr(checkpoint_path),
            "gr_subtarget_report": _ptr(subtarget_path),
            "gr_stop_rule_decision_report": _ptr(stop_rule_path),
            "trend_report": _ptr(trend_path),
            "row_outcome_trend_report": _ptr(row_trend_path),
            "ledger_report": _ptr(ledger_path),
        },
        "non_claim_boundary": "Repository-local GR blocker-moving tranche report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate GR blocker-moving tranche report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "gr_blocker_moving_tranche_20260412_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    declaration_path = ns.declaration if ns.declaration.is_absolute() else (REPO_ROOT / ns.declaration)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_report(declaration_path=declaration_path, captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "gr_blocker_moving_tranche_report: "
        f"classification={payload['summary']['tranche_classification']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
