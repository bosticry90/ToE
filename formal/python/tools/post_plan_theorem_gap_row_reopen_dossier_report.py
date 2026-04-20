from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.post_plan_physics_advancement_target_map_report import _parse_markdown_table


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PLAN_THEOREM_GAP_ROW_REOPEN_DOSSIER_REPORT_20260419_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_THEOREM_GAP_ROW_REOPEN_DOSSIER_STAT_20260419_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_plan_theorem_gap_row_reopen_dossier_stat_20260419_v0.json"
)


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _text(raw: Any) -> str:
    return str(raw).strip() if raw is not None else ""


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    row_policy = dict(declaration.get("row_policy", {}))
    contract = dict(declaration.get("outcome_contract", {}))

    qualification_path = REPO_ROOT / _text(required_inputs.get("fresh_movement_qualification_report"))
    target_map_path = REPO_ROOT / _text(required_inputs.get("post_plan_target_map_report"))
    matrix_path = REPO_ROOT / _text(required_inputs.get("completion_matrix"))
    latest_report_path = REPO_ROOT / _text(required_inputs.get("latest_row_report"))

    qualification_report = _read_json(qualification_path)
    target_map_report = _read_json(target_map_path)
    latest_report = _read_json(latest_report_path)
    matrix_rows = _parse_markdown_table(
        _read_text(matrix_path),
        [
            "row_id",
            "domain",
            "lane",
            "current_status",
            "blocker_class",
            "primary_target",
            "primary_artifact",
            "primary_gate",
            "governance_checkpoint_status",
            "physics_checkpoint_status",
            "gate_runtime_status",
        ],
    )

    row_id = _text(row_policy.get("row_id"))
    route_class_required = _text(row_policy.get("required_route_class"))
    target_row = next((row for row in target_map_report.get("routed_rows", []) if row.get("row_id") == row_id), {})
    matrix_row = next((row for row in matrix_rows if row.get("row_id") == row_id), {})
    latest_terminal_outcome = latest_report.get("summary", {}).get("terminal_outcome")
    selected_row = qualification_report.get("summary", {}).get("selected_row")
    fresh_non_qm_movement_recorded = bool(qualification_report.get("summary", {}).get("fresh_non_qm_movement_recorded"))

    additional_input_summaries: dict[str, Any] = {}
    for key, rel in required_inputs.items():
        if key in {"fresh_movement_qualification_report", "post_plan_target_map_report", "completion_matrix", "latest_row_report"}:
            continue
        path = REPO_ROOT / _text(rel)
        payload = _read_json(path)
        additional_input_summaries[key] = payload.get("summary", {}).get("terminal_outcome") or payload.get("review_basis") or payload.get("schema_id")
    packet05_review_not_eligible = (
        additional_input_summaries.get("stat_packet05_lane_eligibility_review_report")
        == "POST_PLAN_STAT_PACKET05_LANE_ELIGIBILITY_REVIEW_NOT_ELIGIBLE_UNDER_CURRENT_BOOTSTRAP"
    )

    route_class_ok = target_row.get("route_class") == route_class_required
    matrix_ok = bool(matrix_row)
    latest_outcome_ok = bool(latest_terminal_outcome)
    qualification_visible = qualification_report.get("summary", {}).get("default_selected_row") is not None

    requires_non_qm_movement = bool(row_policy.get("requires_non_qm_movement", False))
    reserve_until_resolution = bool(row_policy.get("reserve_until_first_selected_family_resolution", False))
    dormant_package_only = bool(row_policy.get("dormant_package_only", False))
    seam_linked_override_only = bool(row_policy.get("seam_linked_override_only", False))

    non_qm_movement_required_satisfied = (not requires_non_qm_movement) or fresh_non_qm_movement_recorded
    authorization_candidate = selected_row == row_id
    fresh_movement_machine_pinned = authorization_candidate
    admissible_if_authorized = all(
        [
            route_class_ok,
            matrix_ok,
            latest_outcome_ok,
            qualification_visible,
            non_qm_movement_required_satisfied,
            not reserve_until_resolution,
        ]
    )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    if not all([target_row, matrix_row]):
        terminal_outcome = "HOLD_PENDING_POST_PLAN_THEOREM_GAP_ROW_REOPEN_DOSSIER_REPAIR"
        next_action = "RESTORE_ROW_REOPEN_DOSSIER_INPUT_SHAPE_AND_RERUN"
    elif all([route_class_ok, latest_outcome_ok, qualification_visible]):
        terminal_outcome = "POST_PLAN_THEOREM_GAP_ROW_REOPEN_DOSSIER_MATERIALIZED"
        next_action = (
            f"REVIEW_SUCCESSOR_AUTHORIZATION_FOR_{row_id}"
            if authorization_candidate
            else (
                f"RETAIN_{row_id}_DOSSIER_UNOPENED_WHILE_STAT_PACKET05_LANE_REMAINS_INELIGIBLE"
                if packet05_review_not_eligible
                else f"RETAIN_{row_id}_DOSSIER_UNOPENED_UNTIL_FRESH_MOVEMENT_IS_MACHINE_PINNED"
            )
        )
    else:
        terminal_outcome = "POST_PLAN_THEOREM_GAP_ROW_REOPEN_DOSSIER_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_ROW_REOPEN_DOSSIER_EVIDENCE_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = _text(contract.get("default_outcome"))

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "route_class_alignment_ok": route_class_ok,
            "completion_matrix_row_present": matrix_ok,
            "latest_terminal_outcome_present": latest_outcome_ok,
            "qualification_surface_visible": qualification_visible,
            "non_qm_movement_requirement_satisfied": non_qm_movement_required_satisfied,
            "single_terminal_outcome_rule_declared": _text(contract.get("single_terminal_outcome_rule"))
            == "EXACTLY_ONE_ALLOWED_POST_PLAN_THEOREM_GAP_ROW_REOPEN_DOSSIER_OUTCOME",
            "no_loop_rule_declared": _text(contract.get("no_loop_rule")) == "ONE_ROW_DOSSIER_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "authorization_candidate_requires_fresh_selection": (not authorization_candidate) or fresh_movement_machine_pinned,
                "reserve_rows_remain_closed_without_resolution": (not reserve_until_resolution) or not admissible_if_authorized,
            },
            "inputs": {
                "row_id": row_id,
                "policy_class": _text(row_policy.get("policy_class")),
                "default_rank": row_policy.get("default_rank"),
                "selected_row": selected_row,
                "current_target_doc": matrix_row.get("primary_target"),
                "current_target_artifact": matrix_row.get("primary_artifact"),
                "current_target_gate": matrix_row.get("primary_gate"),
                "latest_terminal_outcome": latest_terminal_outcome,
                "historical_no_change_count": row_policy.get("historical_no_change_count"),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "row_id": row_id,
            "policy_class": _text(row_policy.get("policy_class")),
            "default_rank": row_policy.get("default_rank"),
            "route_class": target_row.get("route_class"),
            "current_target_doc": matrix_row.get("primary_target"),
            "current_target_artifact": matrix_row.get("primary_artifact"),
            "current_target_gate": matrix_row.get("primary_gate"),
            "latest_terminal_outcome": latest_terminal_outcome,
            "historical_no_change_count": row_policy.get("historical_no_change_count"),
            "exhausted_family_history": row_policy.get("exhausted_family_history", []),
            "fresh_movement_hypothesis": _text(row_policy.get("fresh_movement_hypothesis")),
            "measurable_blocker_delta_criterion": _text(row_policy.get("measurable_blocker_delta_criterion")),
            "bounded_execution_surface_declaration": _text(row_policy.get("bounded_execution_surface_declaration")),
            "bounded_execution_surface_gate": _text(row_policy.get("bounded_execution_surface_gate")),
            "explicit_exhaustion_fallback": _text(row_policy.get("explicit_exhaustion_fallback")),
            "authorization_candidate": authorization_candidate,
            "fresh_movement_machine_pinned": fresh_movement_machine_pinned,
            "requires_non_qm_movement": requires_non_qm_movement,
            "non_qm_movement_required_satisfied": non_qm_movement_required_satisfied,
            "seam_linked_override_only": seam_linked_override_only,
            "dormant_package_only": dormant_package_only,
            "reserve_until_first_selected_family_resolution": reserve_until_resolution,
            "admissible_if_authorized": admissible_if_authorized,
            "additional_bound_surfaces": additional_input_summaries,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "fresh_movement_qualification_report": _ptr(qualification_path),
            "post_plan_target_map_report": _ptr(target_map_path),
            "completion_matrix": _ptr(matrix_path),
            "latest_row_report": _ptr(latest_report_path),
        },
        "non_claim_boundary": "Repository-local theorem-gap row reopen dossier only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate a post-plan theorem-gap row reopen dossier report.")
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
        "post_plan_theorem_gap_row_reopen_dossier_report: "
        f"row_id={payload['summary']['row_id']} terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
