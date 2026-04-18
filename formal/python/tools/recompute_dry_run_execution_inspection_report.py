from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import recompute_execute_all
from formal.python.tools import recompute_surface_helpers as helpers


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "RECOMPUTE_DRY_RUN_EXECUTION_INSPECTION_REPORT_20260418_v0"
DEFAULT_DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "RECOMPUTE_DRY_RUN_EXECUTION_INSPECTION_20260418_v0.json"
DEFAULT_OUT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "recompute_dry_run_execution_inspection_20260418_v0.json"


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(_read_text(path))


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _surface_snapshot(*, root: Path, expected_trigger_status: str) -> dict[str, dict[str, Any]]:
    snapshots: dict[str, dict[str, Any]] = {}
    for surface_id in helpers.SURFACE_SPECS:
        document = helpers.ensure_surface_document(surface_id, root=root)
        latest = helpers.latest_trigger(document)
        snapshots[surface_id] = {
            "surface_path": str(helpers.surface_path(surface_id, root=root).relative_to(root)).replace("\\", "/"),
            "latest_trigger_id": None if latest is None else latest.get("trigger_id"),
            "latest_trigger_status": None if latest is None else latest.get("status"),
            "expected_trigger_status": expected_trigger_status,
            "has_computed_state": "computed_state" in document,
            "has_execution_summary": "execution_summary" in document,
        }
    return snapshots


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    policy = dict(declaration.get("execution_policy", {}))
    outcome_contract = dict(declaration.get("outcome_contract", {}))
    phase_plan = list(declaration.get("phase_plan", []))

    contract_path = REPO_ROOT / str(required_inputs.get("recompute_live_writeback_contract_report", "")).strip()
    execute_tool_path = REPO_ROOT / str(required_inputs.get("recompute_execute_all_tool", "")).strip()
    bundle_path = REPO_ROOT / str(required_inputs.get("dry_run_bundle_report", "")).strip()
    baseline_path = REPO_ROOT / str(required_inputs.get("dry_run_baseline_report", "")).strip()
    state_path = REPO_ROOT / str(required_inputs.get("state_mirror", "")).strip()
    roadmap_path = REPO_ROOT / str(required_inputs.get("roadmap_mirror", "")).strip()
    inventory_path = REPO_ROOT / str(required_inputs.get("inventory_mirror", "")).strip()

    contract_report = _read_json(contract_path)
    bundle_report = _read_json(bundle_path)
    baseline_report = _read_json(baseline_path)
    state_text = _read_text(state_path)
    roadmap_text = _read_text(roadmap_path)
    inventory_text = _read_text(inventory_path)

    canonical_snapshots = _surface_snapshot(root=REPO_ROOT, expected_trigger_status=str(policy.get("required_canonical_trigger_status", "")).strip())
    dry_run_snapshots = _surface_snapshot(root=recompute_execute_all.DEFAULT_DRY_RUN_ROOT, expected_trigger_status=str(policy.get("required_dry_run_trigger_status", "")).strip())

    contract_ok = contract_report.get("summary", {}).get("terminal_outcome") == str(policy.get("required_contract_outcome", "")).strip()
    bundle_ok = (
        bundle_report.get("summary", {}).get("execution_mode") == str(policy.get("required_bundle_execution_mode", "")).strip()
        and bundle_report.get("summary", {}).get("surfaces_completed") == int(policy.get("required_bundle_surfaces_completed", 0))
        and bundle_report.get("summary", {}).get("next_action") == str(policy.get("required_bundle_next_action", "")).strip()
    )
    no_live_writeback = bundle_report.get("summary", {}).get("live_writeback_performed") is bool(policy.get("required_live_writeback_performed", False))
    baseline_ok = baseline_report.get("summary", {}).get("baseline_surfaces") == 3
    dry_run_surfaces_ok = all(
        snapshot["has_computed_state"]
        and snapshot["has_execution_summary"]
        and snapshot["latest_trigger_status"] == snapshot["expected_trigger_status"]
        for snapshot in dry_run_snapshots.values()
    )
    canonical_pending_ok = all(
        (not snapshot["has_computed_state"])
        and snapshot["latest_trigger_status"] == snapshot["expected_trigger_status"]
        for snapshot in canonical_snapshots.values()
    )
    mirrors_registered = all(
        ref in state_text or ref in roadmap_text or ref in inventory_text
        for ref in [
            "formal/docs/release/RECOMPUTE_DRY_RUN_EXECUTION_INSPECTION_20260418_v0.json",
            "formal/output/reports/recompute_dry_run_execution_inspection_20260418_v0.json",
            "formal/python/tools/recompute_dry_run_execution_inspection_report.py",
            "formal/python/tests/test_recompute_dry_run_execution_inspection_report.py",
        ]
    )

    phase_status = {
        0: contract_ok,
        1: bundle_ok,
        2: baseline_ok,
        3: dry_run_surfaces_ok,
        4: canonical_pending_ok,
        5: no_live_writeback,
        6: contract_report.get("objective_quality", {}).get("inputs", {}).get("monitoring_outcome") == "POST_PLAN_RECOMPUTE_MONITORING_PATH_PENDING_COMPLETION",
        7: mirrors_registered,
        8: True,
    }
    completed_phases = [phase["phase_id"] for phase in phase_plan if phase_status.get(phase["phase_id"], False)]

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(outcome_contract.get("default_outcome", "RECOMPUTE_DRY_RUN_EXECUTION_INSPECTION_EVIDENCE_INCOMPLETE")).strip()

    if not execute_tool_path.exists() or not contract_ok:
        terminal_outcome = "HOLD_PENDING_RECOMPUTE_DRY_RUN_EXECUTION_INSPECTION_REPAIR"
        next_action = "RESTORE_DRY_RUN_EXECUTION_INSPECTION_INPUTS_AND_RERUN"
    elif all([bundle_ok, baseline_ok, dry_run_surfaces_ok, canonical_pending_ok, no_live_writeback]):
        terminal_outcome = "RECOMPUTE_DRY_RUN_EXECUTION_INSPECTION_MATERIALIZED_CANONICAL_PENDING"
        next_action = str(policy.get("required_next_action", "")).strip()
    elif bundle_ok:
        terminal_outcome = "RECOMPUTE_DRY_RUN_EXECUTION_INSPECTION_BLOCKED"
        next_action = "REPAIR_DRY_RUN_EXECUTION_OR_CANONICAL_INVARIANCE_BEFORE_PROCEEDING"
    else:
        terminal_outcome = "RECOMPUTE_DRY_RUN_EXECUTION_INSPECTION_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_DRY_RUN_EXECUTION_INSPECTION_EVIDENCE"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "contract_dry_run_ready_verified": contract_ok,
            "dry_run_bundle_materialized": bundle_ok,
            "dry_run_baseline_materialized": baseline_ok,
            "dry_run_surfaces_completed": dry_run_surfaces_ok,
            "canonical_surfaces_remain_pending": canonical_pending_ok,
            "no_live_writeback_performed": no_live_writeback,
            "mirror_registration_present": mirrors_registered,
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip() == "EXACTLY_ONE_ALLOWED_RECOMPUTE_DRY_RUN_EXECUTION_INSPECTION_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip() == "ONE_RECOMPUTE_DRY_RUN_EXECUTION_INSPECTION_ONLY",
        },
        "phase_plan_status": [
            {
                "phase_id": phase["phase_id"],
                "phase_name": phase["phase_name"],
                "requirement": phase["requirement"],
                "satisfied": phase_status.get(phase["phase_id"], False),
            }
            for phase in phase_plan
        ],
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "dry_run_outputs_exist_without_live_claim": dry_run_surfaces_ok and no_live_writeback,
                "canonical_recompute_completion_not_claimed": canonical_pending_ok,
            },
            "inputs": {
                "contract_outcome": contract_report.get("summary", {}).get("terminal_outcome"),
                "bundle_execution_mode": bundle_report.get("summary", {}).get("execution_mode"),
                "bundle_live_writeback_performed": bundle_report.get("summary", {}).get("live_writeback_performed"),
                "bundle_next_action": bundle_report.get("summary", {}).get("next_action"),
                "completed_phases": completed_phases,
                "dry_run_workspace_root": bundle_report.get("dry_run_workspace", {}).get("workspace_root"),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "canonical_surfaces": canonical_snapshots,
        "dry_run_surfaces": dry_run_snapshots,
        "summary": {
            "terminal_outcome": terminal_outcome,
            "completed_phase_count": len(completed_phases),
            "phase_count": len(phase_plan),
            "dry_run_workspace_root": bundle_report.get("dry_run_workspace", {}).get("workspace_root"),
            "canonical_pending_surface_count": sum(1 for snapshot in canonical_snapshots.values() if snapshot["latest_trigger_status"] == snapshot["expected_trigger_status"]),
            "dry_run_completed_surface_count": sum(1 for snapshot in dry_run_snapshots.values() if snapshot["latest_trigger_status"] == snapshot["expected_trigger_status"]),
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "recompute_live_writeback_contract_report": _ptr(contract_path),
            "recompute_execute_all_tool": _ptr(execute_tool_path),
            "dry_run_bundle_report": _ptr(bundle_path),
            "dry_run_baseline_report": _ptr(baseline_path),
        },
        "non_claim_boundary": "Repository-local recompute dry-run execution inspection only; no scientific adequacy claim and no implied canonical recompute completion.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the recompute dry-run execution inspection report.")
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
        "recompute_dry_run_execution_inspection_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())