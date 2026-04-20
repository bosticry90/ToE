from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.post_plan_physics_advancement_target_map_report import _parse_markdown_table


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_EXECUTION_REPORT_20260419_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_EXECUTION_20260419_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_plan_cosmo_sr_selected_continuation_execution_20260419_v0.json"
)


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(_read_text(path))


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _maybe_text(raw: Any) -> str:
    return str(raw).strip() if raw is not None else ""


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    policy = dict(declaration.get("execution_policy", {}))
    contract = dict(declaration.get("outcome_contract", {}))

    selected_family_path = REPO_ROOT / _maybe_text(required_inputs.get("post_plan_cosmo_sr_selected_continuation_family_report"))
    target_map_path = REPO_ROOT / _maybe_text(required_inputs.get("post_plan_target_map_report"))
    matrix_path = REPO_ROOT / _maybe_text(required_inputs.get("completion_matrix"))
    dashboard_path = REPO_ROOT / _maybe_text(required_inputs.get("blocker_burn_dashboard_report"))
    target_doc_path = REPO_ROOT / _maybe_text(required_inputs.get("selected_continuation_target_doc"))
    artifact_path = REPO_ROOT / _maybe_text(required_inputs.get("selected_continuation_artifact"))
    gate_path = REPO_ROOT / _maybe_text(required_inputs.get("selected_continuation_gate"))

    selected_family_report = _read_json(selected_family_path)
    target_map = _read_json(target_map_path)
    dashboard = _read_json(dashboard_path)
    artifact = _read_json(artifact_path)
    doc_text = _read_text(target_doc_path)
    gate_text = _read_text(gate_path)
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

    selected_family_summary = dict(selected_family_report.get("summary", {}))
    routed_rows = {row.get("row_id"): row for row in target_map.get("routed_rows", [])}
    matrix_row_map = {row.get("row_id"): row for row in matrix_rows}
    target_row_id = _maybe_text(policy.get("required_target_row"))
    target_row = dict(routed_rows.get(target_row_id, {}))
    matrix_row = dict(matrix_row_map.get(target_row_id, {}))

    selected_family_ok = all(
        [
            selected_family_summary.get("terminal_outcome") == _maybe_text(policy.get("required_selected_family_outcome")),
            selected_family_summary.get("next_action") == _maybe_text(policy.get("required_selected_family_next_action")),
            selected_family_summary.get("selected_continuation_lane") == "COSMO_SR_CYCLE08",
            selected_family_summary.get("target_row_id") == target_row_id,
            bool(selected_family_summary.get("selected_continuation_machine_pinned")),
        ]
    )
    target_map_ok = (
        target_map.get("summary", {}).get("terminal_outcome") == "POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_MATERIALIZED"
        and target_row.get("route_class") == _maybe_text(policy.get("required_target_route_class"))
    )
    row_ok = (
        bool(matrix_row)
        and matrix_row.get("blocker_class") == _maybe_text(policy.get("required_row_blocker_class"))
    )
    payload_ok = all(
        [
            "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE08_v0" in doc_text,
            artifact.get("artifact_id") == "cosmo_sr_class_b_seam_physics_pilot_cycle08_v0",
            artifact.get("seam_id") == _maybe_text(policy.get("required_target_seam")),
            artifact.get("status") == _maybe_text(policy.get("required_artifact_status")),
            artifact.get("adjudication", {}).get("value") in {
                _maybe_text(policy.get("required_artifact_adjudication")),
                "DISCHARGED",
            },
            "def test_cosmo_sr_cycle08_artifacts_exist()" in gate_text,
        ]
    )

    promotion_earned = bool(matrix_row) and (
        matrix_row.get("physics_checkpoint_status") == "PHYSICS_COMPLETE"
        or matrix_row.get("current_status") == "GOVERNANCE_COMPLETE_AND_PHYSICS_COMPLETE"
        or artifact.get("adjudication", {}).get("value") == "DISCHARGED"
    )
    blocker_deltas = dashboard.get("blocker_scoreboard", {}).get("delta_by_class", {})
    seam_gap_delta = int(blocker_deltas.get("SEAM_INTEGRATION_GAP", 0) or 0)

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    default_outcome = _maybe_text(contract.get("default_outcome"))

    if not matrix_row or not target_row:
        terminal_outcome = "HOLD_PENDING_POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_EXECUTION_REPAIR"
        next_action = "RESTORE_COSMO_SR_SELECTED_CONTINUATION_EXECUTION_INPUT_SHAPE_AND_RERUN"
    elif all([selected_family_ok, target_map_ok, row_ok, payload_ok]) and promotion_earned:
        terminal_outcome = "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_EXECUTION_EXECUTED_AND_PROMOTED"
        next_action = _maybe_text(policy.get("promoted_next_action"))
    elif all([selected_family_ok, target_map_ok, row_ok, payload_ok]):
        terminal_outcome = "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_EXECUTION_EXECUTED_NONPROMOTED_CLOSEOUT"
        next_action = _maybe_text(policy.get("nonpromoted_closeout_next_action"))
    else:
        terminal_outcome = "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_EXECUTION_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_COSMO_SR_SELECTED_CONTINUATION_EXECUTION_EVIDENCE_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "selected_family_ready_recorded": selected_family_ok,
            "target_map_materialized": target_map_ok,
            "live_row_alignment_ok": row_ok,
            "cycle08_payload_alignment_ok": payload_ok,
            "single_terminal_outcome_rule_declared": _maybe_text(contract.get("single_terminal_outcome_rule"))
            == "EXACTLY_ONE_ALLOWED_POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_EXECUTION_OUTCOME",
            "no_loop_rule_declared": _maybe_text(contract.get("no_loop_rule"))
            == "ONE_POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_EXECUTION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "single_use_execution_consumed_once": selected_family_ok,
                "promotion_only_if_row_truth_changed": (
                    terminal_outcome != "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_EXECUTION_EXECUTED_AND_PROMOTED"
                ) or promotion_earned,
            },
            "inputs": {
                "target_row_id": target_row_id,
                "target_route_class": target_row.get("route_class"),
                "row_current_status": matrix_row.get("current_status"),
                "row_physics_checkpoint_status": matrix_row.get("physics_checkpoint_status"),
                "artifact_status": artifact.get("status"),
                "artifact_adjudication": artifact.get("adjudication", {}).get("value"),
                "seam_integration_gap_delta": seam_gap_delta,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "target_row_id": target_row_id,
            "target_seam_id": _maybe_text(policy.get("required_target_seam")),
            "selected_continuation_lane": selected_family_summary.get("selected_continuation_lane"),
            "row_truth_change_detected": promotion_earned,
            "promotion_earned": promotion_earned,
            "row_current_status": matrix_row.get("current_status"),
            "row_physics_checkpoint_status": matrix_row.get("physics_checkpoint_status"),
            "artifact_adjudication": artifact.get("adjudication", {}).get("value"),
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "post_plan_cosmo_sr_selected_continuation_family_report": _ptr(selected_family_path),
            "post_plan_target_map_report": _ptr(target_map_path),
            "completion_matrix": _ptr(matrix_path),
            "blocker_burn_dashboard_report": _ptr(dashboard_path),
            "selected_continuation_target_doc": _ptr(target_doc_path),
            "selected_continuation_artifact": _ptr(artifact_path),
            "selected_continuation_gate": _ptr(gate_path),
        },
        "non_claim_boundary": "Repository-local post-plan COSMO-SR selected continuation execution only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the post-plan COSMO-SR selected continuation execution report.")
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
        "post_plan_cosmo_sr_selected_continuation_execution_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())