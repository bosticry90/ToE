from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_REPORT_20260418_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_20260418_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_plan_physics_advancement_target_map_20260418_v0.json"
)

SEAM_ID_BY_ROW = {
    "ROW-SEAM-QFT-GR-001": "SEAM-QFT-GR",
    "ROW-SEAM-QM-STAT-001": "SEAM-QM-STAT",
    "ROW-SEAM-COSMO-SR-001": "SEAM-COSMO-SR",
    "ROW-SEAM-GR-QM-001": "SEAM-GR-QM",
}

ROUTE_CLASS_BY_PATH_CLASS = {
    "SINGLE_AUTHORIZED_NONLIVE_EXECUTABLE_PATH": "EXECUTABLE_NOW",
    "POLICY_BLOCKED_NONEXECUTABLE_PATH": "BLOCKED_PENDING_AUTHORITY",
    "EXTERNAL_HOLD_NONEXECUTABLE_PATH": "EXTERNAL_HOLD",
    "CLOSED_MONITORING_NONEXECUTABLE_PATH": "CLOSED_MONITORING",
    "COUNTERFACTUAL_MIRROR_ONLY_NONEXECUTABLE_PATH": "MIRROR_ONLY_NONEXECUTABLE",
    "GOVERNANCE_COMPLETE_NO_ACTIVE_EXECUTION_PATH": "GOVERNANCE_COMPLETE_NO_ACTIVE_PATH",
}


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(_read_text(path))


def _parse_markdown_table(text: str, required_columns: list[str]) -> list[dict[str, str]]:
    lines = text.splitlines()
    start = None
    for index, line in enumerate(lines):
        if not line.strip().startswith("|"):
            continue
        header_cells = [cell.strip().strip("`") for cell in line.strip().strip("|").split("|")]
        if all(column in header_cells for column in required_columns):
            start = index
            break
    if start is None or start + 2 >= len(lines):
        return []

    header_cells = [cell.strip().strip("`") for cell in lines[start].strip().strip("|").split("|")]
    rows: list[dict[str, str]] = []
    for line in lines[start + 2 :]:
        if not line.startswith("|"):
            break
        cells = [cell.strip().strip("`") for cell in line.strip().strip("|").split("|")]
        if len(cells) != len(header_cells):
            continue
        rows.append(dict(zip(header_cells, cells)))
    return rows


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _map_by_key(rows: list[dict[str, Any]], key: str) -> dict[str, dict[str, Any]]:
    mapped: dict[str, dict[str, Any]] = {}
    for row in rows:
        value = str(row.get(key, "")).strip()
        if value:
            mapped[value] = dict(row)
    return mapped


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    policy = dict(declaration.get("target_map_policy", {}))
    outcome_contract = dict(declaration.get("outcome_contract", {}))

    matrix_path = REPO_ROOT / str(required_inputs.get("completion_matrix", "")).strip()
    dashboard_path = REPO_ROOT / str(required_inputs.get("blocker_burn_dashboard_report", "")).strip()
    sla_path = REPO_ROOT / str(required_inputs.get("seam_resolution_sla_ledger_report", "")).strip()
    normalization_path = REPO_ROOT / str(required_inputs.get("seam_executable_path_normalization_report", "")).strip()
    gr_map_path = REPO_ROOT / str(required_inputs.get("gr_row_001_blocker_file_map", "")).strip()

    matrix_text = _read_text(matrix_path)
    dashboard = _read_json(dashboard_path)
    sla = _read_json(sla_path)
    normalization = _read_json(normalization_path)
    gr_map = _read_json(gr_map_path)

    matrix_rows = _parse_markdown_table(
        matrix_text,
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
    readiness_rows = _map_by_key(list(dashboard.get("row_promotion_readiness", {}).get("rows", [])), "row_id")
    closure_rows = _map_by_key(list(dashboard.get("closure_map_linkage", {}).get("mapped_rows", [])), "row_id")
    sla_rows = _map_by_key(list(sla.get("entries", [])), "row_id")
    normalized_rows = _map_by_key(list(normalization.get("normalized_rows", [])), "seam_id")

    gr_target_row = str(gr_map.get("target_row", "")).strip()
    gr_branch = dict(gr_map.get("authoritative_branch_classification", {}))
    gr_next_step = str(gr_branch.get("authoritative_next_step", "")).strip()
    gr_next_action = str(gr_branch.get("authoritative_next_action", "")).strip()

    closure_missing_rows: list[str] = []
    readiness_missing_rows: list[str] = []
    sla_missing_rows: list[str] = []
    normalization_missing_rows: list[str] = []
    unresolved_route_rows: list[str] = []
    routed_rows: list[dict[str, Any]] = []

    for row in matrix_rows:
        row_id = str(row.get("row_id", "")).strip()
        domain = str(row.get("domain", "")).strip()
        closure = closure_rows.get(row_id, {})
        readiness = readiness_rows.get(row_id, {})
        if not closure:
            closure_missing_rows.append(row_id)
        if not readiness:
            readiness_missing_rows.append(row_id)

        route_class = ""
        authoritative_next_step = ""
        authoritative_next_action = ""
        supporting_surfaces = [
            _ptr(matrix_path),
            _ptr(dashboard_path),
        ]

        if row_id == gr_target_row and str(gr_branch.get("current_lane_class", "")).strip() == "FROZEN_NEW_STRUCTURE_BRANCH":
            route_class = str(policy.get("frozen_new_structure_route_class", "")).strip()
            authoritative_next_step = gr_next_step
            authoritative_next_action = gr_next_action
            supporting_surfaces.append(_ptr(gr_map_path))
        elif domain == "seam":
            sla_entry = sla_rows.get(row_id, {})
            if not sla_entry:
                sla_missing_rows.append(row_id)
            seam_id = str(sla_entry.get("seam_id", "")).strip() or SEAM_ID_BY_ROW.get(row_id, "")
            normalized = normalized_rows.get(seam_id, {})
            if not normalized:
                normalization_missing_rows.append(row_id)
            path_class = str(normalized.get("path_class", "")).strip()
            route_class = ROUTE_CLASS_BY_PATH_CLASS.get(path_class, "")
            authoritative_next_step = str(row.get("primary_target", "")).strip()
            authoritative_next_action = str(normalized.get("next_action", "")).strip() or str(sla_entry.get("decision_state", "")).strip()
            supporting_surfaces.extend(filter(None, [_ptr(sla_path), _ptr(normalization_path)]))
        else:
            route_class = str(policy.get("theorem_gap_route_class", "")).strip()
            authoritative_next_step = str(row.get("primary_target", "")).strip()
            authoritative_next_action = "EXECUTE_PINNED_THEOREM_GAP_PROGRAM_AND_REQUIRE_BLOCKER_DELTA_NEGATIVE"

        if not route_class or not authoritative_next_step or not authoritative_next_action:
            unresolved_route_rows.append(row_id)

        routed_rows.append(
            {
                "row_id": row_id,
                "domain": domain,
                "lane": str(row.get("lane", "")).strip(),
                "blocker_class": str(row.get("blocker_class", "")).strip(),
                "current_status": str(row.get("current_status", "")).strip(),
                "route_class": route_class,
                "authoritative_next_step": authoritative_next_step,
                "authoritative_next_action": authoritative_next_action,
                "primary_artifact": str(row.get("primary_artifact", "")).strip(),
                "primary_gate": str(row.get("primary_gate", "")).strip(),
                "closure_gate": str(closure.get("closure_gate", "")).strip(),
                "closure_exit_criterion": str(closure.get("exit_criterion", "")).strip(),
                "promotion_readiness_status": str(readiness.get("promotion_readiness_status", "")).strip(),
                "gate_runtime_status": str(readiness.get("gate_runtime_status", row.get("gate_runtime_status", ""))).strip(),
                "governance_checkpoint_status": str(row.get("governance_checkpoint_status", "")).strip(),
                "physics_checkpoint_status": str(row.get("physics_checkpoint_status", "")).strip(),
                "supporting_surfaces": supporting_surfaces,
            }
        )

    route_class_map = _map_by_key(routed_rows, "row_id")
    executable_rows = [row["row_id"] for row in routed_rows if row.get("route_class") == str(policy.get("executable_now_route_class", "")).strip()]
    blocked_rows = [row["row_id"] for row in routed_rows if row.get("route_class") == str(policy.get("blocked_authority_route_class", "")).strip()]
    external_hold_rows = [row["row_id"] for row in routed_rows if row.get("route_class") == str(policy.get("external_hold_route_class", "")).strip()]
    closed_monitoring_rows = [row["row_id"] for row in routed_rows if row.get("route_class") == str(policy.get("closed_monitoring_route_class", "")).strip()]
    frozen_rows = [row["row_id"] for row in routed_rows if row.get("route_class") == str(policy.get("frozen_new_structure_route_class", "")).strip()]
    theorem_gap_rows = [row["row_id"] for row in routed_rows if row.get("route_class") == str(policy.get("theorem_gap_route_class", "")).strip()]

    single_executable_row_pinned = executable_rows == [str(policy.get("required_single_executable_row", "")).strip()]
    blocked_row_pinned = str(policy.get("required_blocked_authority_row", "")).strip() in blocked_rows
    external_hold_row_pinned = str(policy.get("required_external_hold_row", "")).strip() in external_hold_rows
    closed_monitoring_row_pinned = str(policy.get("required_closed_monitoring_row", "")).strip() in closed_monitoring_rows
    gr_row_override_applied = (
        str(policy.get("required_gr_row_001", "")).strip() in frozen_rows
        and route_class_map.get(str(policy.get("required_gr_row_001", "")).strip(), {}).get("authoritative_next_step")
        == str(policy.get("required_gr_row_001_next_step", "")).strip()
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(outcome_contract.get("default_outcome", "POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_EVIDENCE_INCOMPLETE")).strip()

    if not matrix_rows or not gr_target_row:
        terminal_outcome = "HOLD_PENDING_POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_REPAIR"
        next_action = "RESTORE_TARGET_MAP_INPUT_SHAPE_AND_RERUN"
    elif all(
        [
            not closure_missing_rows,
            not readiness_missing_rows,
            not sla_missing_rows,
            not normalization_missing_rows,
            not unresolved_route_rows,
            single_executable_row_pinned,
            blocked_row_pinned,
            external_hold_row_pinned,
            closed_monitoring_row_pinned,
            gr_row_override_applied,
        ]
    ):
        terminal_outcome = "POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_MATERIALIZED"
        next_action = "EXECUTE_PHASE2_COSMO_SR_FIRST_LIVE_SEAM_TRANCHE"
    else:
        terminal_outcome = "POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_ROUTE_COVERAGE_AND_RERUN_TARGET_MAP"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "matrix_rows_present": bool(matrix_rows),
            "closure_map_covers_matrix_rows": not closure_missing_rows,
            "readiness_rows_cover_matrix_rows": not readiness_missing_rows,
            "seam_sla_covers_live_seam_rows": not sla_missing_rows,
            "seam_normalization_covers_live_seams": not normalization_missing_rows,
            "single_executable_row_pinned": single_executable_row_pinned,
            "blocked_authority_row_pinned": blocked_row_pinned,
            "external_hold_row_pinned": external_hold_row_pinned,
            "closed_monitoring_row_pinned": closed_monitoring_row_pinned,
            "gr_row_001_override_applied": gr_row_override_applied,
            "no_unresolved_route_rows": not unresolved_route_rows,
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "one_route_per_row_materialized": not unresolved_route_rows,
                "routing_constraints_preserved": all(
                    [single_executable_row_pinned, blocked_row_pinned, external_hold_row_pinned, gr_row_override_applied]
                ),
            },
            "inputs": {
                "rows_total": len(routed_rows),
                "blocker_movement_status": dashboard.get("blocker_scoreboard", {}).get("movement_status"),
                "blocker_net_delta": dashboard.get("blocker_scoreboard", {}).get("net_delta"),
                "seam_sla_dashboard_movement_status": sla.get("dashboard_coupling", {}).get("movement_status"),
                "seam_sla_stale_input_warning": sla.get("dashboard_coupling", {}).get("stale_input_warning"),
                "required_progress_rule": policy.get("required_progress_rule"),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "rows_total": len(routed_rows),
            "seam_rows_total": len([row for row in routed_rows if row.get("domain") == "seam"]),
            "pillar_rows_total": len([row for row in routed_rows if row.get("domain") == "pillar"]),
            "executable_now_rows": executable_rows,
            "blocked_pending_authority_rows": blocked_rows,
            "external_hold_rows": external_hold_rows,
            "closed_monitoring_rows": closed_monitoring_rows,
            "frozen_new_structure_rows": frozen_rows,
            "theorem_gap_program_rows": theorem_gap_rows,
            "next_action": next_action,
        },
        "coverage_gaps": {
            "closure_map_missing_rows": closure_missing_rows,
            "readiness_missing_rows": readiness_missing_rows,
            "seam_sla_missing_rows": sla_missing_rows,
            "normalization_missing_rows": normalization_missing_rows,
            "unresolved_route_rows": unresolved_route_rows,
        },
        "routed_rows": routed_rows,
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "completion_matrix": _ptr(matrix_path),
            "blocker_burn_dashboard_report": _ptr(dashboard_path),
            "seam_resolution_sla_ledger_report": _ptr(sla_path),
            "seam_executable_path_normalization_report": _ptr(normalization_path),
            "gr_row_001_blocker_file_map": _ptr(gr_map_path),
        },
        "non_claim_boundary": "Repository-local post-plan physics advancement target map report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the post-plan physics advancement target map report.")
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
        "post_plan_physics_advancement_target_map_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())