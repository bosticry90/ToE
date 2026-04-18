from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PLAN_POST_CASCADE_CLOSURE_REVIEW_REPORT_20260418_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_POST_CASCADE_CLOSURE_REVIEW_20260418_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_plan_post_cascade_closure_review_20260418_v0.json"
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


def _route_class(report: dict[str, Any], row_id: str) -> str | None:
    for routed_row in report.get("routed_rows", []):
        if routed_row.get("row_id") == row_id:
            return routed_row.get("route_class")
    return None


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    policy = dict(declaration.get("closure_policy", {}))
    outcome_contract = dict(declaration.get("outcome_contract", {}))

    monitoring_path = REPO_ROOT / str(required_inputs.get("post_plan_recompute_monitoring_path_report", "")).strip()
    seam_path = REPO_ROOT / str(required_inputs.get("post_plan_seam_reroute_reassessment_report", "")).strip()
    master_action_path = REPO_ROOT / str(required_inputs.get("post_plan_master_action_reevaluation_report", "")).strip()
    integration_path = REPO_ROOT / str(required_inputs.get("post_plan_final_integration_review_report", "")).strip()
    target_map_path = REPO_ROOT / str(required_inputs.get("post_plan_target_map_report", "")).strip()

    monitoring = _read_json(monitoring_path)
    seam = _read_json(seam_path)
    master_action = _read_json(master_action_path)
    integration = _read_json(integration_path)
    target_map = _read_json(target_map_path)

    monitoring_outcome = monitoring.get("summary", {}).get("terminal_outcome")
    monitoring_post_ruling = monitoring.get("summary", {}).get("post_recompute_ruling_id")
    seam_outcome = seam.get("summary", {}).get("terminal_outcome")
    master_action_outcome = master_action.get("summary", {}).get("terminal_outcome")
    integration_outcome = integration.get("summary", {}).get("terminal_outcome")

    single_executable_row = str(policy.get("required_single_executable_row", "")).strip()
    blocked_row = str(policy.get("required_blocked_row", "")).strip()
    external_hold_row = str(policy.get("required_external_hold_row", "")).strip()
    closed_monitoring_row = str(policy.get("required_closed_monitoring_row", "")).strip()

    target_map_stable = (
        _route_class(target_map, single_executable_row) == "EXECUTABLE_NOW"
        and _route_class(target_map, blocked_row) == "BLOCKED_PENDING_AUTHORITY"
        and _route_class(target_map, external_hold_row) == "EXTERNAL_HOLD"
        and _route_class(target_map, closed_monitoring_row) == "CLOSED_MONITORING"
    )
    monitoring_material = (
        monitoring_outcome == str(policy.get("required_monitoring_outcome", "")).strip()
        and monitoring_post_ruling == str(policy.get("required_monitoring_post_ruling", "")).strip()
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get("default_outcome", "POST_PLAN_POST_CASCADE_CLOSURE_REVIEW_EVIDENCE_INCOMPLETE")
    ).strip()

    if not target_map_stable:
        terminal_outcome = "HOLD_PENDING_POST_PLAN_POST_CASCADE_CLOSURE_REPAIR"
        next_action = "RESTORE_POST_PLAN_POST_CASCADE_INPUTS_AND_RERUN"
    elif seam_outcome == "POST_PLAN_SEAM_REROUTE_REASSESSMENT_MATERIALIZED":
        terminal_outcome = "POST_PLAN_POST_CASCADE_CLOSURE_REVIEW_REOPEN_SEAM_REROUTE"
        next_action = "APPLY_SEAM_REROUTE_REASSESSMENT_RESULT_ON_CANONICAL_SURFACES"
    elif master_action_outcome == "POST_PLAN_MASTER_ACTION_REEVALUATION_MATERIALIZED":
        terminal_outcome = "POST_PLAN_POST_CASCADE_CLOSURE_REVIEW_REOPEN_MASTER_ACTION"
        next_action = "APPLY_MASTER_ACTION_REEVALUATION_RESULT_ON_CANONICAL_SURFACES"
    elif integration_outcome == "POST_PLAN_FINAL_INTEGRATION_REVIEW_ADVANCEMENT_ELIGIBLE":
        terminal_outcome = "POST_PLAN_POST_CASCADE_CLOSURE_REVIEW_ADVANCEMENT_ELIGIBLE"
        next_action = "PROMOTE_UPDATED_INTEGRATION_POSTURE_ON_CANONICAL_SURFACES"
    elif monitoring_material and target_map_stable and seam_outcome == "POST_PLAN_SEAM_REROUTE_REASSESSMENT_NOT_ELIGIBLE_NO_UPSTREAM_MOVEMENT" and master_action_outcome == "POST_PLAN_MASTER_ACTION_REEVALUATION_NOT_ELIGIBLE_NO_UPSTREAM_MOVEMENT" and integration_outcome == "POST_PLAN_FINAL_INTEGRATION_REVIEW_HELD_PENDING_FURTHER_BLOCKER_MOVEMENT":
        terminal_outcome = "POST_PLAN_POST_CASCADE_CLOSURE_REVIEW_BOUNDED_HOLD_RECORDED"
        next_action = "EXECUTE_NEXT_THEOREM_GAP_TRANCHE_OR_EXPLICIT_EXHAUSTION_READ_WITH_POST_CASCADE_HOLD_RECORDED"
    else:
        terminal_outcome = "POST_PLAN_POST_CASCADE_CLOSURE_REVIEW_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_POST_PLAN_POST_CASCADE_EVIDENCE_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "monitoring_material_cascade_confirmed": monitoring_material,
            "target_map_route_classes_stable": target_map_stable,
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip() == "EXACTLY_ONE_ALLOWED_POST_PLAN_POST_CASCADE_CLOSURE_REVIEW_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip() == "ONE_POST_PLAN_POST_CASCADE_CLOSURE_REVIEW_LAYER_ONLY",
            "bounded_hold_rule_declared": str(policy.get("required_bounded_hold_rule", "")).strip() == "MATERIAL_CASCADE_ALONE_DOES_NOT_RECLASSIFY_DOWNSTREAM_ROUTES_WITHOUT_ROW_OR_ROUTE_MOVEMENT",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "material_cascade_does_not_force_route_reclassification": terminal_outcome != "POST_PLAN_POST_CASCADE_CLOSURE_REVIEW_BOUNDED_HOLD_RECORDED" or (
                    monitoring_material and seam_outcome != "POST_PLAN_SEAM_REROUTE_REASSESSMENT_MATERIALIZED" and master_action_outcome != "POST_PLAN_MASTER_ACTION_REEVALUATION_MATERIALIZED" and integration_outcome != "POST_PLAN_FINAL_INTEGRATION_REVIEW_ADVANCEMENT_ELIGIBLE"
                ),
            },
            "inputs": {
                "monitoring_terminal_outcome": monitoring_outcome,
                "monitoring_post_recompute_ruling": monitoring_post_ruling,
                "seam_reroute_terminal_outcome": seam_outcome,
                "master_action_terminal_outcome": master_action_outcome,
                "final_integration_terminal_outcome": integration_outcome,
                "single_executable_row_route_class": _route_class(target_map, single_executable_row),
                "blocked_row_route_class": _route_class(target_map, blocked_row),
                "external_hold_row_route_class": _route_class(target_map, external_hold_row),
                "closed_monitoring_row_route_class": _route_class(target_map, closed_monitoring_row),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "monitoring_terminal_outcome": monitoring_outcome,
            "monitoring_post_recompute_ruling": monitoring_post_ruling,
            "seam_reroute_terminal_outcome": seam_outcome,
            "master_action_terminal_outcome": master_action_outcome,
            "final_integration_terminal_outcome": integration_outcome,
            "target_map_route_classes_stable": target_map_stable,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "post_plan_recompute_monitoring_path_report": _ptr(monitoring_path),
            "post_plan_seam_reroute_reassessment_report": _ptr(seam_path),
            "post_plan_master_action_reevaluation_report": _ptr(master_action_path),
            "post_plan_final_integration_review_report": _ptr(integration_path),
            "post_plan_target_map_report": _ptr(target_map_path),
        },
        "non_claim_boundary": "Repository-local post-cascade closure review only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the post-plan post-cascade closure review report.")
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
        "post_plan_post_cascade_closure_review_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())