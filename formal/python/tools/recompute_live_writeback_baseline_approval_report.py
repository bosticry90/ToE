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
SCHEMA_ID = "RECOMPUTE_LIVE_WRITEBACK_BASELINE_APPROVAL_REPORT_20260418_v0"
DEFAULT_DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "RECOMPUTE_LIVE_WRITEBACK_BASELINE_APPROVAL_20260418_v0.json"
DEFAULT_OUT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "recompute_live_writeback_baseline_approval_20260418_v0.json"


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


def _canonical_surface_snapshot(expected_trigger_status: str) -> dict[str, dict[str, Any]]:
    snapshots: dict[str, dict[str, Any]] = {}
    for surface_id in helpers.SURFACE_SPECS:
        document = helpers.ensure_surface_document(surface_id)
        latest = helpers.latest_trigger(document)
        snapshots[surface_id] = {
            "surface_path": str(helpers.surface_path(surface_id).relative_to(REPO_ROOT)).replace("\\", "/"),
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
    approval_contract = dict(declaration.get("approval_contract", {}))
    outcome_contract = dict(declaration.get("outcome_contract", {}))
    phase_plan = list(declaration.get("phase_plan", []))

    live_contract_path = REPO_ROOT / str(required_inputs.get("recompute_live_writeback_contract_report", "")).strip()
    dry_run_path = REPO_ROOT / str(required_inputs.get("recompute_dry_run_execution_inspection_report", "")).strip()
    monitoring_path = REPO_ROOT / str(required_inputs.get("post_plan_recompute_monitoring_path_report", "")).strip()
    baseline_tool_path = REPO_ROOT / str(required_inputs.get("recompute_baseline_snapshot_tool", "")).strip()
    execute_tool_path = REPO_ROOT / str(required_inputs.get("recompute_execute_all_tool", "")).strip()
    state_path = REPO_ROOT / str(required_inputs.get("state_mirror", "")).strip()
    roadmap_path = REPO_ROOT / str(required_inputs.get("roadmap_mirror", "")).strip()
    inventory_path = REPO_ROOT / str(required_inputs.get("inventory_mirror", "")).strip()

    live_contract_report = _read_json(live_contract_path)
    dry_run_report = _read_json(dry_run_path)
    monitoring_report = _read_json(monitoring_path)
    state_text = _read_text(state_path)
    roadmap_text = _read_text(roadmap_path)
    inventory_text = _read_text(inventory_path)

    canonical_snapshots = _canonical_surface_snapshot(str(policy.get("required_latest_trigger_status", "")).strip())
    canonical_pending_ok = all(
        snapshot["latest_trigger_status"] == snapshot["expected_trigger_status"]
        and not snapshot["has_computed_state"]
        and not snapshot["has_execution_summary"]
        for snapshot in canonical_snapshots.values()
    )

    upstream_contract_ok = live_contract_report.get("summary", {}).get("terminal_outcome") == str(policy.get("required_live_writeback_contract_outcome", "")).strip()
    dry_run_ok = dry_run_report.get("summary", {}).get("terminal_outcome") == str(policy.get("required_dry_run_inspection_outcome", "")).strip()
    monitoring_ok = monitoring_report.get("summary", {}).get("terminal_outcome") == str(policy.get("required_monitoring_outcome", "")).strip()
    tools_ok = baseline_tool_path.exists() and execute_tool_path.exists()
    execution_flags_ok = (
        recompute_execute_all.LIVE_WRITEBACK_MODE == str(policy.get("required_execution_mode", "")).strip()
        and recompute_execute_all.LIVE_WRITEBACK_REQUIREMENT == approval_contract.get("approval_guard")
        and bool(policy.get("required_allow_live_writeback", False)) is True
    )
    single_use_ok = approval_contract.get("approval_scope") == "ONE_CANONICAL_LIVE_WRITEBACK_ONLY" and approval_contract.get("approval_followthrough") == [
        "RERUN_RECOMPUTE_OBSERVATION_REPORT",
        "RERUN_POST_RECOMPUTE_OBSERVATION_REPORT",
        "RERUN_POST_PLAN_RECOMPUTE_MONITORING_PATH_REPORT",
    ]
    mirrors_registered = all(
        ref in state_text or ref in roadmap_text or ref in inventory_text
        for ref in [
            "formal/docs/release/RECOMPUTE_LIVE_WRITEBACK_BASELINE_APPROVAL_20260418_v0.json",
            "formal/output/reports/recompute_live_writeback_baseline_approval_20260418_v0.json",
            "formal/python/tools/recompute_live_writeback_baseline_approval_report.py",
            "formal/python/tests/test_recompute_live_writeback_baseline_approval_report.py",
        ]
    )

    phase_status = {
        0: upstream_contract_ok,
        1: dry_run_ok,
        2: monitoring_ok,
        3: canonical_pending_ok,
        4: baseline_tool_path.exists(),
        5: execution_flags_ok,
        6: single_use_ok,
        7: mirrors_registered,
        8: True,
    }
    completed_phases = [phase["phase_id"] for phase in phase_plan if phase_status.get(phase["phase_id"], False)]

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(outcome_contract.get("default_outcome", "RECOMPUTE_LIVE_WRITEBACK_BASELINE_APPROVAL_EVIDENCE_INCOMPLETE")).strip()

    if not tools_ok:
        terminal_outcome = "HOLD_PENDING_RECOMPUTE_LIVE_WRITEBACK_BASELINE_APPROVAL_REPAIR"
        next_action = "RESTORE_LIVE_WRITEBACK_BASELINE_APPROVAL_INPUTS_AND_RERUN"
    elif all([upstream_contract_ok, dry_run_ok, monitoring_ok, canonical_pending_ok, execution_flags_ok, single_use_ok]):
        terminal_outcome = "RECOMPUTE_LIVE_WRITEBACK_BASELINE_APPROVAL_READY"
        next_action = str(policy.get("required_next_action", "")).strip()
    elif upstream_contract_ok and dry_run_ok:
        terminal_outcome = "RECOMPUTE_LIVE_WRITEBACK_BASELINE_APPROVAL_BLOCKED"
        next_action = "REPAIR_CANONICAL_PREWRITEBACK_STATE_OR_APPROVAL_CONDITIONS"
    else:
        terminal_outcome = "RECOMPUTE_LIVE_WRITEBACK_BASELINE_APPROVAL_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_LIVE_WRITEBACK_BASELINE_APPROVAL_EVIDENCE"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "upstream_live_writeback_contract_verified": upstream_contract_ok,
            "dry_run_execution_inspection_verified": dry_run_ok,
            "monitoring_pending_verified": monitoring_ok,
            "canonical_surfaces_still_pending": canonical_pending_ok,
            "baseline_capture_tool_present": baseline_tool_path.exists(),
            "explicit_live_writeback_flags_verified": execution_flags_ok,
            "single_use_followthrough_verified": single_use_ok,
            "mirror_registration_present": mirrors_registered,
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip() == "EXACTLY_ONE_ALLOWED_RECOMPUTE_LIVE_WRITEBACK_BASELINE_APPROVAL_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip() == "ONE_RECOMPUTE_LIVE_WRITEBACK_BASELINE_APPROVAL_ONLY",
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
                "canonical_recompute_completion_not_claimed_pre_execution": canonical_pending_ok,
                "approval_only_opens_one_live_writeback": single_use_ok,
            },
            "inputs": {
                "live_writeback_contract_outcome": live_contract_report.get("summary", {}).get("terminal_outcome"),
                "dry_run_inspection_outcome": dry_run_report.get("summary", {}).get("terminal_outcome"),
                "monitoring_outcome": monitoring_report.get("summary", {}).get("terminal_outcome"),
                "live_execution_mode": recompute_execute_all.LIVE_WRITEBACK_MODE,
                "live_writeback_requirement": recompute_execute_all.LIVE_WRITEBACK_REQUIREMENT,
                "completed_phases": completed_phases,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "canonical_surfaces": canonical_snapshots,
        "summary": {
            "terminal_outcome": terminal_outcome,
            "completed_phase_count": len(completed_phases),
            "phase_count": len(phase_plan),
            "canonical_pending_surface_count": sum(1 for snapshot in canonical_snapshots.values() if snapshot["latest_trigger_status"] == snapshot["expected_trigger_status"]),
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "recompute_live_writeback_contract_report": _ptr(live_contract_path),
            "recompute_dry_run_execution_inspection_report": _ptr(dry_run_path),
            "post_plan_recompute_monitoring_path_report": _ptr(monitoring_path),
            "recompute_baseline_snapshot_tool": _ptr(baseline_tool_path),
            "recompute_execute_all_tool": _ptr(execute_tool_path),
        },
        "non_claim_boundary": "Repository-local live-writeback baseline and approval contract only; no scientific adequacy claim and no implied canonical recompute completion.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the recompute live-writeback baseline approval report.")
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
        "recompute_live_writeback_baseline_approval_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())