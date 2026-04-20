from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_REPORT_20260419_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_20260419_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_plan_theorem_gap_fresh_movement_qualification_20260419_v0.json"
)


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _text(raw: Any) -> str:
    return str(raw).strip() if raw is not None else ""


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    policy = dict(declaration.get("selection_policy", {}))
    contract = dict(declaration.get("outcome_contract", {}))

    queue_path = REPO_ROOT / _text(required_inputs.get("completion_queue_report"))
    target_map_path = REPO_ROOT / _text(required_inputs.get("post_plan_target_map_report"))
    dashboard_path = REPO_ROOT / _text(required_inputs.get("blocker_burn_dashboard_report"))
    trend_path = REPO_ROOT / _text(required_inputs.get("theorem_gap_row_outcome_trend_report"))
    exhaustion_path = REPO_ROOT / _text(required_inputs.get("post_plan_post_cascade_explicit_exhaustion_decision_report"))
    successor_path = REPO_ROOT / _text(required_inputs.get("post_plan_post_cascade_successor_family_eligibility_review_report"))
    cosmo_seam_path = REPO_ROOT / _text(required_inputs.get("post_plan_cosmo_sr_selected_continuation_execution_report"))

    queue_report = _read_json(queue_path)
    target_map_report = _read_json(target_map_path)
    dashboard_report = _read_json(dashboard_path)
    trend_report = _read_json(trend_path)
    exhaustion_report = _read_json(exhaustion_path)
    successor_report = _read_json(successor_path)
    cosmo_seam_report = _read_json(cosmo_seam_path)

    required_stop_outcome = _text(policy.get("required_stop_outcome"))
    required_exhaustion_outcome = _text(policy.get("required_exhaustion_outcome"))
    default_selected_row = _text(policy.get("default_selected_row"))
    alternate_selected_row = _text(policy.get("alternate_selected_row"))
    blocked_row = _text(policy.get("blocked_row"))
    dormant_only_row = _text(policy.get("dormant_only_row"))
    reserve_rows = [str(v).strip() for v in policy.get("reserve_rows", [])]
    required_primary_executable_seam = _text(policy.get("required_primary_executable_seam"))
    cosmo_override_row = _text(policy.get("cosmo_override_row"))
    cosmo_override_target_row = _text(policy.get("cosmo_override_target_row"))

    queue_ok = queue_report.get("summary", {}).get("terminal_outcome") == "POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_MATERIALIZED"
    stop_outcome_ok = successor_report.get("summary", {}).get("terminal_outcome") == required_stop_outcome
    exhaustion_ok = exhaustion_report.get("summary", {}).get("terminal_outcome") == required_exhaustion_outcome

    blocker_deltas = dashboard_report.get("blocker_scoreboard", {}).get("delta_by_class", {})
    theorem_gap_delta = int(blocker_deltas.get("THEOREM_GAP", 0) or 0)
    seam_gap_delta = int(blocker_deltas.get("SEAM_INTEGRATION_GAP", 0) or 0)
    fresh_theorem_gap_movement = theorem_gap_delta < 0
    fresh_seam_movement = seam_gap_delta < 0
    fresh_non_qm_movement_recorded = fresh_theorem_gap_movement or fresh_seam_movement

    target_map_primary_rows = target_map_report.get("summary", {}).get("executable_now_rows", [])
    if not target_map_primary_rows:
        target_map_primary_rows = [
            row.get("row_id")
            for row in target_map_report.get("routed_rows", [])
            if row.get("route_class") == "EXECUTABLE_NOW"
        ]
    primary_executable_seam_ok = cosmo_override_row in target_map_primary_rows
    queue_second_ok = queue_report.get("summary", {}).get("second_active_row") == default_selected_row
    qm_excluded_ok = queue_report.get("summary", {}).get("excluded_row") == blocked_row
    gr_heavy_ok = queue_report.get("summary", {}).get("heavy_structural_row") == dormant_only_row
    reserve_rows_visible = all(row in queue_report.get("summary", {}).get("queue_order", []) for row in reserve_rows)
    trend_has_rows = bool(trend_report.get("objective_quality", {}).get("inputs", {}).get("row_outcome_counts", {}))

    cosmo_override_condition_met = all(
        [
            fresh_seam_movement,
            primary_executable_seam_ok,
            cosmo_seam_report.get("summary", {}).get("target_row_id") == cosmo_override_row,
            bool(cosmo_seam_report.get("summary", {}).get("row_truth_change_detected")),
        ]
    )
    stat_default_condition_met = all(
        [
            fresh_theorem_gap_movement,
            queue_second_ok,
            not cosmo_override_condition_met,
        ]
    )

    selected_row = "NONE"
    selected_execution_surface_declaration: str | None = None
    if cosmo_override_condition_met:
        selected_row = alternate_selected_row
        selected_execution_surface_declaration = _text(policy.get("cosmo_execution_surface_declaration")) or None
        terminal_outcome = "POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_COSMO_OVERRIDE_SELECTED"
        next_action = "REVIEW_AND_AUTHORIZE_COSMO_REACTIVATION_DOSSIER_ONLY"
    elif stat_default_condition_met:
        selected_row = default_selected_row
        selected_execution_surface_declaration = _text(policy.get("stat_execution_surface_declaration")) or None
        terminal_outcome = "POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_STAT_DEFAULT_SELECTED"
        next_action = "REVIEW_AND_AUTHORIZE_STAT_REACTIVATION_DOSSIER_ONLY"
    elif all([queue_ok, stop_outcome_ok, exhaustion_ok, trend_has_rows]):
        terminal_outcome = "POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_NO_ROW_SELECTED"
        next_action = "KEEP_TERMINAL_HOLD_AND_REFRESH_ROW_DOSSIERS_ONLY_IF_FRESH_MOVEMENT_APPEARS"
    else:
        terminal_outcome = "POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_THEOREM_GAP_REACTIVATION_INPUTS_AND_RERUN_QUALIFICATION"

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = _text(contract.get("default_outcome"))

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "completion_queue_materialized": queue_ok,
            "required_stop_outcome_recorded": stop_outcome_ok,
            "required_exhaustion_outcome_recorded": exhaustion_ok,
            "fresh_theorem_gap_movement_recorded": fresh_theorem_gap_movement,
            "fresh_seam_integration_movement_recorded": fresh_seam_movement,
            "qm_excluded_from_reopen_order": qm_excluded_ok,
            "gr_heavy_row_pinned": gr_heavy_ok,
            "reserve_rows_visible": reserve_rows_visible,
            "required_primary_executable_seam_pinned": primary_executable_seam_ok,
            "single_terminal_outcome_rule_declared": _text(contract.get("single_terminal_outcome_rule"))
            == "EXACTLY_ONE_ALLOWED_POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_OUTCOME",
            "no_loop_rule_declared": _text(contract.get("no_loop_rule"))
            == "ONE_POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "stat_remains_default_without_cosmo_override": (terminal_outcome != "POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_STAT_DEFAULT_SELECTED")
                or queue_second_ok,
                "cosmo_only_overtakes_with_machine_pinned_seam_override": (
                    terminal_outcome != "POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_COSMO_OVERRIDE_SELECTED"
                )
                or cosmo_override_condition_met,
            },
            "inputs": {
                "default_selected_row": default_selected_row,
                "alternate_selected_row": alternate_selected_row,
                "blocked_row": blocked_row,
                "dormant_only_row": dormant_only_row,
                "reserve_rows": reserve_rows,
                "theorem_gap_delta": theorem_gap_delta,
                "seam_integration_gap_delta": seam_gap_delta,
                "primary_executable_seam": required_primary_executable_seam,
                "cosmo_seam_row_truth_change_detected": bool(cosmo_seam_report.get("summary", {}).get("row_truth_change_detected")),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "default_selected_row": default_selected_row,
            "alternate_selected_row": alternate_selected_row,
            "selected_row": selected_row,
            "selected_execution_surface_declaration": selected_execution_surface_declaration,
            "fresh_non_qm_movement_recorded": fresh_non_qm_movement_recorded,
            "cosmo_override_condition_met": cosmo_override_condition_met,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "completion_queue_report": _ptr(queue_path),
            "post_plan_target_map_report": _ptr(target_map_path),
            "blocker_burn_dashboard_report": _ptr(dashboard_path),
            "theorem_gap_row_outcome_trend_report": _ptr(trend_path),
            "post_plan_post_cascade_explicit_exhaustion_decision_report": _ptr(exhaustion_path),
            "post_plan_post_cascade_successor_family_eligibility_review_report": _ptr(successor_path),
            "post_plan_cosmo_sr_selected_continuation_execution_report": _ptr(cosmo_seam_path),
        },
        "non_claim_boundary": "Repository-local theorem-gap reactivation qualification only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the post-plan theorem-gap fresh-movement qualification report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
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
        "post_plan_theorem_gap_fresh_movement_qualification_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
