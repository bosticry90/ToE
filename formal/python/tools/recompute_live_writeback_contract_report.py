from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import recompute_execute_all


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "RECOMPUTE_LIVE_WRITEBACK_CONTRACT_REPORT_20260418_v0"
DEFAULT_DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "RECOMPUTE_LIVE_WRITEBACK_CONTRACT_20260418_v0.json"
DEFAULT_OUT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "recompute_live_writeback_contract_20260418_v0.json"


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


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    policy = dict(declaration.get("execution_policy", {}))
    outcome_contract = dict(declaration.get("outcome_contract", {}))
    phase_plan = list(declaration.get("phase_plan", []))

    monitoring_path = REPO_ROOT / str(required_inputs.get("post_plan_recompute_monitoring_path_report", "")).strip()
    protocol_path = REPO_ROOT / str(required_inputs.get("monitoring_protocol", "")).strip()
    baseline_tool_path = REPO_ROOT / str(required_inputs.get("recompute_baseline_snapshot_tool", "")).strip()
    execute_tool_path = REPO_ROOT / str(required_inputs.get("recompute_execute_all_tool", "")).strip()
    observation_tool_path = REPO_ROOT / str(required_inputs.get("recompute_observation_tool", "")).strip()
    post_observation_tool_path = REPO_ROOT / str(required_inputs.get("post_recompute_observation_tool", "")).strip()
    state_path = REPO_ROOT / str(required_inputs.get("state_mirror", "")).strip()
    roadmap_path = REPO_ROOT / str(required_inputs.get("roadmap_mirror", "")).strip()
    inventory_path = REPO_ROOT / str(required_inputs.get("inventory_mirror", "")).strip()

    monitoring_report = _read_json(monitoring_path)
    monitoring_protocol = _read_json(protocol_path)
    state_text = _read_text(state_path)
    roadmap_text = _read_text(roadmap_path)
    inventory_text = _read_text(inventory_path)

    monitoring_ok = (
        monitoring_report.get("summary", {}).get("terminal_outcome") == str(policy.get("required_monitoring_outcome", "")).strip()
        and monitoring_report.get("summary", {}).get("next_action") == str(policy.get("required_monitoring_next_action", "")).strip()
    )
    default_mode_ok = recompute_execute_all.DEFAULT_EXECUTION_MODE == str(policy.get("required_default_execution_mode", "")).strip()
    live_mode_ok = recompute_execute_all.LIVE_WRITEBACK_MODE == str(policy.get("required_live_writeback_mode", "")).strip()
    live_guard_ok = recompute_execute_all.LIVE_WRITEBACK_REQUIREMENT == str(policy.get("required_live_writeback_guard", "")).strip()
    bundle_next_action_ok = recompute_execute_all.BUNDLE_NEXT_ACTION == str(policy.get("required_bundle_next_action", "")).strip()
    dry_run_root_ok = recompute_execute_all.DEFAULT_DRY_RUN_ROOT.as_posix().endswith(str(policy.get("required_default_dry_run_root", "")).strip())
    tools_present = all(
        path.exists()
        for path in [baseline_tool_path, execute_tool_path, observation_tool_path, post_observation_tool_path]
    )
    mirror_refs = [
        "formal/docs/release/RECOMPUTE_LIVE_WRITEBACK_CONTRACT_20260418_v0.json",
        "formal/output/reports/recompute_live_writeback_contract_20260418_v0.json",
        "formal/python/tools/recompute_live_writeback_contract_report.py",
        "formal/python/tests/test_recompute_live_writeback_contract_report.py",
    ]
    mirrors_registered = all(ref in state_text or ref in roadmap_text or ref in inventory_text for ref in mirror_refs)

    phase_status = {
        0: declaration_path.exists(),
        1: monitoring_ok,
        2: baseline_tool_path.exists(),
        3: default_mode_ok and live_mode_ok,
        4: dry_run_root_ok,
        5: execute_tool_path.exists() and bundle_next_action_ok,
        6: live_guard_ok,
        7: observation_tool_path.exists() and post_observation_tool_path.exists(),
        8: mirrors_registered,
    }
    completed_phases = [phase["phase_id"] for phase in phase_plan if phase_status.get(phase["phase_id"], False)]

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(outcome_contract.get("default_outcome", "RECOMPUTE_LIVE_WRITEBACK_CONTRACT_EVIDENCE_INCOMPLETE")).strip()

    if not tools_present or not monitoring_report:
        terminal_outcome = "HOLD_PENDING_RECOMPUTE_LIVE_WRITEBACK_CONTRACT_REPAIR"
        next_action = "RESTORE_RECOMPUTE_LIVE_WRITEBACK_CONTRACT_INPUTS_AND_RERUN"
    elif all([monitoring_ok, default_mode_ok, live_mode_ok, live_guard_ok, bundle_next_action_ok, dry_run_root_ok]):
        terminal_outcome = "RECOMPUTE_LIVE_WRITEBACK_CONTRACT_DRY_RUN_READY_LIVE_LOCKED"
        next_action = "RUN_DRY_RUN_BUNDLE_OR_DEFINE_CANONICAL_BASELINE_FOR_LIVE_WRITEBACK"
    elif monitoring_ok and tools_present:
        terminal_outcome = "RECOMPUTE_LIVE_WRITEBACK_CONTRACT_BLOCKED"
        next_action = "REPAIR_RECOMPUTE_EXECUTION_GUARDS_BEFORE_ANY_LIVE_WRITEBACK"
    else:
        terminal_outcome = "RECOMPUTE_LIVE_WRITEBACK_CONTRACT_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_RECOMPUTE_LIVE_WRITEBACK_CONTRACT_EVIDENCE"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "monitoring_pending_state_verified": monitoring_ok,
            "baseline_capture_tool_present": baseline_tool_path.exists(),
            "dry_run_default_enforced": default_mode_ok,
            "live_writeback_mode_declared": live_mode_ok,
            "live_writeback_guard_enforced": live_guard_ok,
            "bundle_next_action_pinned": bundle_next_action_ok,
            "dry_run_root_pinned": dry_run_root_ok,
            "observation_refresh_tools_present": observation_tool_path.exists() and post_observation_tool_path.exists(),
            "mirror_registration_present": mirrors_registered,
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip() == "EXACTLY_ONE_ALLOWED_RECOMPUTE_LIVE_WRITEBACK_CONTRACT_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip() == "ONE_RECOMPUTE_LIVE_WRITEBACK_CONTRACT_ONLY",
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
                "live_writeback_stays_locked_without_explicit_opt_in": live_guard_ok,
                "support_surface_does_not_claim_live_completion": monitoring_report.get("summary", {}).get("terminal_outcome") == str(policy.get("required_monitoring_outcome", "")).strip(),
            },
            "inputs": {
                "monitoring_outcome": monitoring_report.get("summary", {}).get("terminal_outcome"),
                "monitoring_next_action": monitoring_report.get("summary", {}).get("next_action"),
                "monitoring_protocol_no_execution_until": monitoring_protocol.get("no_execution_until"),
                "default_execution_mode": recompute_execute_all.DEFAULT_EXECUTION_MODE,
                "live_writeback_mode": recompute_execute_all.LIVE_WRITEBACK_MODE,
                "live_writeback_requirement": recompute_execute_all.LIVE_WRITEBACK_REQUIREMENT,
                "bundle_next_action": recompute_execute_all.BUNDLE_NEXT_ACTION,
                "completed_phases": completed_phases,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "completed_phase_count": len(completed_phases),
            "phase_count": len(phase_plan),
            "default_execution_mode": recompute_execute_all.DEFAULT_EXECUTION_MODE,
            "live_writeback_guard": recompute_execute_all.LIVE_WRITEBACK_REQUIREMENT,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "post_plan_recompute_monitoring_path_report": _ptr(monitoring_path),
            "monitoring_protocol": _ptr(protocol_path),
            "recompute_baseline_snapshot_tool": _ptr(baseline_tool_path),
            "recompute_execute_all_tool": _ptr(execute_tool_path),
            "recompute_observation_tool": _ptr(observation_tool_path),
            "post_recompute_observation_tool": _ptr(post_observation_tool_path),
        },
        "non_claim_boundary": "Repository-local recompute live-writeback contract only; no scientific adequacy claim and no implied live recompute completion.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the recompute live-writeback contract report.")
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
        "recompute_live_writeback_contract_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())