from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.post_plan_physics_advancement_target_map_report import _parse_markdown_table


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PLAN_COSMO_SR_FIRST_LIVE_SEAM_TRANCHE_REPORT_20260418_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_COSMO_SR_FIRST_LIVE_SEAM_TRANCHE_20260418_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_plan_cosmo_sr_first_live_seam_tranche_20260418_v0.json"
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


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    policy = dict(declaration.get("execution_policy", {}))
    outcome_contract = dict(declaration.get("outcome_contract", {}))

    target_map_path = REPO_ROOT / str(required_inputs.get("post_plan_target_map_report", "")).strip()
    auth_path = REPO_ROOT / str(required_inputs.get("cosmo_sr_bounded_activation_authorization_report", "")).strip()
    matrix_path = REPO_ROOT / str(required_inputs.get("completion_matrix", "")).strip()
    dashboard_path = REPO_ROOT / str(required_inputs.get("blocker_burn_dashboard_report", "")).strip()
    doc_path = REPO_ROOT / str(required_inputs.get("cosmo_sr_target_doc", "")).strip()
    artifact_path = REPO_ROOT / str(required_inputs.get("cosmo_sr_cycle07_artifact", "")).strip()
    gate_path = REPO_ROOT / str(required_inputs.get("cosmo_sr_cycle07_gate", "")).strip()

    target_map = _read_json(target_map_path)
    auth_report = _read_json(auth_path)
    dashboard = _read_json(dashboard_path)
    artifact = _read_json(artifact_path)
    doc_text = _read_text(doc_path)
    _read_text(gate_path)
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
    matrix_row_map = {row["row_id"]: row for row in matrix_rows}

    target_row_id = str(policy.get("required_target_row", "")).strip()
    routed_rows = {row["row_id"]: row for row in target_map.get("routed_rows", [])}
    row = dict(matrix_row_map.get(target_row_id, {}))
    routed_row = dict(routed_rows.get(target_row_id, {}))

    target_map_ok = (
        target_map.get("summary", {}).get("terminal_outcome")
        == "POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_MATERIALIZED"
        and target_map.get("summary", {}).get("executable_now_rows") == [target_row_id]
        and routed_row.get("route_class") == str(policy.get("required_target_route_class", "")).strip()
    )
    authorization_ok = (
        auth_report.get("summary", {}).get("terminal_outcome")
        == str(policy.get("required_authorization_outcome", "")).strip()
        and auth_report.get("summary", {}).get("next_action")
        == str(policy.get("required_authorization_next_action", "")).strip()
        and auth_report.get("summary", {}).get("target_row_id") == target_row_id
    )
    doc_ok = all(
        token in doc_text
        for token in [
            "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE07_v0",
            "COSMO_SR_CYCLE07_STATUS_v0: DODECIC_LOW_Z_ALIGNMENT_AND_EXCLUSION_PINNED_NONCLAIM",
            "formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle07_v0.json",
            "formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle07_gate.py",
        ]
    )
    artifact_adjudication = artifact.get("adjudication", {}).get("value")
    artifact_ok = (
        artifact.get("artifact_id") == "cosmo_sr_class_b_seam_physics_pilot_cycle07_v0"
        and artifact.get("seam_id") == str(policy.get("required_target_seam", "")).strip()
        and artifact_adjudication in {str(policy.get("required_artifact_adjudication", "")).strip(), "DISCHARGED"}
    )
    row_ok = (
        bool(row)
        and row.get("row_id") == target_row_id
        and row.get("blocker_class") == str(policy.get("required_row_blocker_class", "")).strip()
        and row.get("primary_artifact") == _ptr(artifact_path)
        and row.get("primary_gate") == _ptr(gate_path)
    )

    promotion_earned = bool(row) and (
        row.get("physics_checkpoint_status") == "PHYSICS_COMPLETE"
        or row.get("current_status") == "GOVERNANCE_COMPLETE_AND_PHYSICS_COMPLETE"
        or artifact_adjudication == "DISCHARGED"
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(outcome_contract.get("default_outcome", "POST_PLAN_COSMO_SR_FIRST_LIVE_SEAM_TRANCHE_EVIDENCE_INCOMPLETE")).strip()

    if not row or not routed_row:
        terminal_outcome = "HOLD_PENDING_POST_PLAN_COSMO_SR_TRANCHE_REPAIR"
        next_action = "RESTORE_COSMO_SR_TRANCHE_INPUT_SHAPE_AND_RERUN"
    elif all([target_map_ok, authorization_ok, doc_ok, artifact_ok, row_ok]) and promotion_earned:
        terminal_outcome = "POST_PLAN_COSMO_SR_FIRST_LIVE_SEAM_TRANCHE_EXECUTED_AND_PROMOTED"
        next_action = "RERUN_TARGET_MAP_AND_REEVALUATE_DOWNSTREAM_PHASES"
    elif all([target_map_ok, authorization_ok, doc_ok, artifact_ok, row_ok]):
        terminal_outcome = "POST_PLAN_COSMO_SR_FIRST_LIVE_SEAM_TRANCHE_EXECUTED_NONPROMOTED"
        next_action = "RETAIN_COSMO_SR_AS_SOLE_EXECUTABLE_ROW_AND_REQUIRE_NEW_ROW_MOVEMENT_BEFORE_REROUTE"
    else:
        terminal_outcome = "POST_PLAN_COSMO_SR_FIRST_LIVE_SEAM_TRANCHE_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_POST_PLAN_COSMO_SR_TRANCHE_EVIDENCE_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "target_map_materialized": target_map_ok,
            "authorization_surface_matches": authorization_ok,
            "cycle07_doc_tokens_present": doc_ok,
            "cycle07_artifact_alignment_ok": artifact_ok,
            "cycle07_row_alignment_ok": row_ok,
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_POST_PLAN_COSMO_SR_TRANCHE_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_POST_PLAN_COSMO_SR_TRANCHE_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "single_executable_row_boundary_preserved": target_map_ok,
                "promotion_only_if_row_truth_changed": (terminal_outcome != "POST_PLAN_COSMO_SR_FIRST_LIVE_SEAM_TRANCHE_EXECUTED_AND_PROMOTED") or promotion_earned,
            },
            "inputs": {
                "target_row_id": target_row_id,
                "target_route_class": routed_row.get("route_class"),
                "authorization_outcome": auth_report.get("summary", {}).get("terminal_outcome"),
                "artifact_adjudication": artifact_adjudication,
                "row_current_status": row.get("current_status"),
                "row_physics_checkpoint_status": row.get("physics_checkpoint_status"),
                "blocker_movement_status": dashboard.get("blocker_scoreboard", {}).get("movement_status"),
                "blocker_net_delta": dashboard.get("blocker_scoreboard", {}).get("net_delta"),
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
            "target_seam_id": str(policy.get("required_target_seam", "")).strip(),
            "target_route_class": routed_row.get("route_class"),
            "row_truth_change_detected": promotion_earned,
            "promotion_earned": promotion_earned,
            "blocker_class": row.get("blocker_class"),
            "row_current_status": row.get("current_status"),
            "row_physics_checkpoint_status": row.get("physics_checkpoint_status"),
            "artifact_adjudication": artifact_adjudication,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "post_plan_target_map_report": _ptr(target_map_path),
            "cosmo_sr_bounded_activation_authorization_report": _ptr(auth_path),
            "completion_matrix": _ptr(matrix_path),
            "blocker_burn_dashboard_report": _ptr(dashboard_path),
            "cosmo_sr_target_doc": _ptr(doc_path),
            "cosmo_sr_cycle07_artifact": _ptr(artifact_path),
            "cosmo_sr_cycle07_gate": _ptr(gate_path),
        },
        "non_claim_boundary": "Repository-local post-plan COSMO-SR first live seam tranche measurement only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the post-plan COSMO-SR first live seam tranche report.")
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
    print(f"post_plan_cosmo_sr_first_live_seam_tranche_report: terminal_outcome={payload['summary']['terminal_outcome']} out={out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())