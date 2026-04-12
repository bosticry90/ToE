from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_BLOCKER_MOVING_TRANCHE_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "QM_BLOCKER_MOVING_TRANCHE_PACKET_20260411_v0.json"
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
    verification = dict(checkpoint.get("verification", {}))
    focused_gate = dict(verification.get("focused_gate", {}))
    full_governance = dict(verification.get("full_governance", {}))
    checkpoint_ladder = dict(verification.get("checkpoint_ladder", {}))
    focused_result = str(focused_gate.get("result", "")).lower()
    acceptance_posture = str(checkpoint.get("acceptance_posture", "")).strip()
    return (
        "passed" in focused_result
        and bool(full_governance.get("governance_gate_ok", False))
        and bool(checkpoint_ladder.get("governance_gate_ok", False))
        and acceptance_posture == "TGC77_EXECUTION_AND_VALIDATION_COMPLETE_PENDING_BOUNDED_COMMIT"
    )


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    movement_policy = dict(declaration.get("movement_policy", {}))

    execution_checkpoint_path = REPO_ROOT / str(required_inputs.get("execution_checkpoint", ""))
    qm_rework_report_path = REPO_ROOT / str(required_inputs.get("qm_rework_report", ""))
    qm_subtarget_report_path = REPO_ROOT / str(required_inputs.get("qm_subtarget_report", ""))
    trend_report_path = REPO_ROOT / str(required_inputs.get("trend_report", ""))
    row_outcome_trend_path = REPO_ROOT / str(required_inputs.get("row_outcome_trend_report", ""))
    ledger_report_path = REPO_ROOT / str(required_inputs.get("ledger_report", ""))
    linkage_registry_path = REPO_ROOT / str(required_inputs.get("linkage_registry", ""))

    execution_checkpoint = _read_json(execution_checkpoint_path)
    qm_rework_report = _read_json(qm_rework_report_path)
    qm_subtarget_report = _read_json(qm_subtarget_report_path)
    trend_report = _read_json(trend_report_path)
    row_outcome_trend = _read_json(row_outcome_trend_path)
    ledger_report = _read_json(ledger_report_path)
    linkage_registry = _read_json(linkage_registry_path)

    row_id = str(declaration.get("row_id", "")).strip()
    subtarget_id = str(declaration.get("subtarget_id", "")).strip()
    tranche_id = str(declaration.get("tranche_id", "")).strip()

    theorem_gap_prior = int(trend_report.get("blocker_counts", {}).get("prior", {}).get("THEOREM_GAP", 0) or 0)
    theorem_gap_current = int(
        trend_report.get("blocker_counts", {}).get("current", {}).get("THEOREM_GAP", theorem_gap_prior) or 0
    )
    theorem_gap_delta = theorem_gap_current - theorem_gap_prior

    row_counts = row_outcome_trend.get("objective_quality", {}).get("inputs", {}).get("row_outcome_counts", {})
    current_row_counts = dict(row_counts.get(row_id, {})) if isinstance(row_counts, dict) else {}
    baseline_inputs = qm_rework_report.get("objective_quality", {}).get("inputs", {})
    baseline_row_counts = {
        "success": int(baseline_inputs.get("target_row_success_count", 0) or 0),
        "no_change": int(baseline_inputs.get("target_row_no_change_count", 0) or 0),
        "failure": int(baseline_inputs.get("target_row_failure_count", 0) or 0),
    }
    baseline_row_counts["total"] = (
        baseline_row_counts["success"] + baseline_row_counts["no_change"] + baseline_row_counts["failure"]
    )
    current_row_counts_normalized = {
        "success": int(current_row_counts.get("success", 0) or 0),
        "no_change": int(current_row_counts.get("no_change", 0) or 0),
        "failure": int(current_row_counts.get("failure", 0) or 0),
        "total": int(current_row_counts.get("total", 0) or 0),
    }
    target_row_outcome_delta = {
        key: current_row_counts_normalized[key] - baseline_row_counts.get(key, 0)
        for key in ["success", "no_change", "failure", "total"]
    }

    actual_blocker_state_change = str(ledger_report.get("actual_blocker_state_change", "")).strip()
    blocker_state_token_changed = actual_blocker_state_change not in {"", "NO_DELTA_DETECTED_ROUTE_TO_REWORK"}
    blocker_state_token_delta = 1 if blocker_state_token_changed else 0

    qm_subtarget_inputs = qm_subtarget_report.get("objective_quality", {}).get("inputs", {})
    qm_subtarget_target_row = str(qm_subtarget_inputs.get("target_row", "")).strip()

    linkage_entries = [
        entry
        for entry in linkage_registry.get("entries", [])
        if str(entry.get("target_row", "")).strip() == row_id
    ]
    linkage_entry_present = any(
        str(entry.get("tranche_id", "")).strip() in {"TGC-77", "R5-QM-REWORK-001", "R6-QM-SUBTARGET-001"}
        for entry in linkage_entries
    )

    execution_valid = _execution_valid(execution_checkpoint)
    theorem_gap_delta_lt_0 = theorem_gap_delta < 0
    theorem_gap_state_changed = theorem_gap_delta != 0
    target_row_success_increment_gt_0 = target_row_outcome_delta["success"] > 0
    all_movement_signals_false = not any(
        [theorem_gap_delta_lt_0, target_row_success_increment_gt_0, blocker_state_token_changed]
    )

    if execution_valid and (theorem_gap_delta_lt_0 or target_row_success_increment_gt_0):
        tranche_classification = "QM_BLOCKER_MOVED"
        next_action = "CONTINUE_QM_BLOCKER_MOVING_PROGRAM"
    elif execution_valid and all_movement_signals_false:
        tranche_classification = "QM_VALID_BUT_NONMOVING"
        next_action = "EMIT_QM_RULING_AND_REFRESH_ATTACK_CLASS_SELECTION"
    else:
        tranche_classification = "QM_TRANCHE_INCOMPLETE"
        next_action = "RESTORE_QM_TRANCHE_PRECONDITIONS_AND_REVIEW_ONCE"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "packet_declares_qm_target_row": row_id == "ROW-PILLAR-QM-001",
            "packet_declares_subtarget": subtarget_id == "QM_PACKET04_THRESHOLD_ALIGNMENT_SUBPROBLEM_v0",
            "execution_checkpoint_present": execution_checkpoint_path.exists(),
            "execution_checkpoint_valid": execution_valid,
            "qm_subtarget_report_matches_target_row": qm_subtarget_target_row == row_id,
            "linkage_entry_present": linkage_entry_present,
            "movement_policy_declared": bool(movement_policy),
        },
        "objective_quality": {
            "criteria": {
                "theorem_gap_delta_lt_0": theorem_gap_delta_lt_0,
                "target_row_success_increment_gt_0": target_row_success_increment_gt_0,
                "blocker_state_token_changed": blocker_state_token_changed,
                "all_movement_signals_false": all_movement_signals_false,
                "tranche_classification_materialized": tranche_classification in {
                    "QM_BLOCKER_MOVED",
                    "QM_VALID_BUT_NONMOVING",
                    "QM_TRANCHE_INCOMPLETE",
                },
            },
            "inputs": {
                "tranche_id": tranche_id,
                "row_id": row_id,
                "subtarget_id": subtarget_id,
                "theorem_gap_prior": theorem_gap_prior,
                "theorem_gap_current": theorem_gap_current,
                "theorem_gap_delta": theorem_gap_delta,
                "theorem_gap_state_changed": theorem_gap_state_changed,
                "baseline_row_counts": baseline_row_counts,
                "current_row_counts": current_row_counts_normalized,
                "target_row_outcome_delta": target_row_outcome_delta,
                "actual_blocker_state_change": actual_blocker_state_change,
                "blocker_state_token_delta": blocker_state_token_delta,
                "movement_signals": {
                    "theorem_gap_delta_lt_0": theorem_gap_delta_lt_0,
                    "target_row_success_increment_gt_0": target_row_success_increment_gt_0,
                    "blocker_state_token_changed": blocker_state_token_changed,
                },
                "success_rule": movement_policy.get("success_rule"),
                "failure_rule": movement_policy.get("failure_rule"),
                "no_loop_rule": movement_policy.get("no_loop_rule"),
            },
            "summary": {
                "all_criteria_satisfied": tranche_classification != "QM_TRANCHE_INCOMPLETE",
                "phase_status": "COMPLETE" if tranche_classification != "QM_TRANCHE_INCOMPLETE" else "INCOMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "tranche_id": tranche_id,
            "row_id": row_id,
            "subtarget_id": subtarget_id,
            "tranche_classification": tranche_classification,
            "theorem_gap_delta": theorem_gap_delta,
            "target_row_outcome_delta": target_row_outcome_delta,
            "blocker_state_token_delta": blocker_state_token_delta,
            "success_rule": movement_policy.get("success_rule"),
            "failure_rule": movement_policy.get("failure_rule"),
            "no_loop_rule": movement_policy.get("no_loop_rule"),
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "execution_checkpoint": _ptr(execution_checkpoint_path),
            "qm_rework_report": _ptr(qm_rework_report_path),
            "qm_subtarget_report": _ptr(qm_subtarget_report_path),
            "trend_report": _ptr(trend_report_path),
            "row_outcome_trend_report": _ptr(row_outcome_trend_path),
            "ledger_report": _ptr(ledger_report_path),
            "linkage_registry": _ptr(linkage_registry_path),
        },
        "non_claim_boundary": "Repository-local QM blocker-moving tranche report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate QM blocker-moving tranche report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "qm_blocker_moving_tranche_20260411_v0.json",
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
        "qm_blocker_moving_tranche_report: "
        f"classification={payload['summary']['tranche_classification']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
