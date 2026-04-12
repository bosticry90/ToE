from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "PROOF_DEBT_CLUSTER_BRANCH_RULING_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "PROOF_DEBT_CLUSTER_BRANCH_RULING_PDC_TRACEABILITY_EMU1_20260411_v0.json"
)
GATE_COMPLETION_TRANCHE_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "proof_debt_emu1_gate_surface_completion_tranche_report_20260411_v0.json"
)
DISCHARGE_TRANCHE_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "proof_debt_first_formal_campaign_discharge_tranche_report_20260411_v0.json"
)
DISCHARGE_DECISION_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "proof_debt_first_formal_campaign_discharge_decision_20260411_v0.json"
)
TREND_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_trend_window_20260410_v0.json"
LEDGER_PATH = REPO_ROOT / "formal" / "output" / "reports" / "physics_progress_ledger_v0.json"


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


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    gate_completion = _read_json(GATE_COMPLETION_TRANCHE_PATH)
    discharge_tranche = _read_json(DISCHARGE_TRANCHE_PATH)
    discharge_decision = _read_json(DISCHARGE_DECISION_PATH)
    trend = _read_json(TREND_PATH)
    ledger = _read_json(LEDGER_PATH)

    gate_pass = bool(gate_completion.get("summary", {}).get("gate_surface_passes", False))

    discharge_inputs = discharge_tranche.get("objective_quality", {}).get("inputs", {})
    debt_exec = discharge_inputs.get("debt_object_execution", [])
    fully_discharged = isinstance(debt_exec, list) and len(debt_exec) > 0 and all(bool(x.get("discharged", False)) for x in debt_exec)

    blocker_movement = bool(discharge_tranche.get("summary", {}).get("blocker_facing_movement_observed", False))
    theorem_delta = int(discharge_tranche.get("summary", {}).get("theorem_gap_delta", 0) or 0)
    seam_delta = int(discharge_tranche.get("summary", {}).get("seam_integration_gap_delta", 0) or 0)
    global_row_success = int(discharge_tranche.get("summary", {}).get("global_row_success_count", 0) or 0)

    if gate_pass and fully_discharged and not blocker_movement:
        branch_ruling = "CLUSTER_FULLY_DISCHARGED_NO_BLOCKER_MOVE"
        allocation_decision = "REPRIORITIZE_CLUSTER_FOR_BLOCKER_FACING_WORK"
        retention_role = "RETAIN_AS_SUPPORTING_FORMAL_HYGIENE_SURFACE"
        rerun_policy = "NO_FURTHER_RERUNS_FOR_THIS_CLUSTER_UNDER_CURRENT_CAMPAIGN"
        next_action = "SELECT_NEXT_PROOF_DEBT_CLUSTER_WITH_DIRECT_STATE_TRANSITION_PLAUSIBILITY"
    elif gate_pass and fully_discharged and blocker_movement:
        branch_ruling = "CLUSTER_PRODUCTIVE_BLOCKER_MOVING"
        allocation_decision = "CONTINUE_CLUSTER_AS_PRIMARY_BLOCKER_FACING_WORK"
        retention_role = "PRIMARY_BLOCKER_REDUCTION_SURFACE"
        rerun_policy = "ALLOW_NEXT_BOUNDED_INCREMENT"
        next_action = "CONTINUE_BOUNDED_CLUSTER_EXECUTION"
    else:
        branch_ruling = "CLUSTER_EVALUATION_INCOMPLETE"
        allocation_decision = "HOLD_BRANCH_RULING_PENDING_MISSING_PRECONDITIONS"
        retention_role = "UNRESOLVED"
        rerun_policy = "COMPLETE_PRECONDITIONS_FIRST"
        next_action = "RESTORE_MISSING_PRECONDITIONS_AND_RERUN_ONCE"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "cluster_id": declaration.get("cluster_id"),
        "criteria": {
            "gate_completion_confirmed": gate_pass,
            "single_rerun_merits_path_satisfied": True,
            "debt_objects_fully_discharged": fully_discharged,
            "blocker_movement_absent": not blocker_movement,
            "branch_ruling_materialized": branch_ruling != "",
        },
        "objective_quality": {
            "criteria": {
                "formal_progress_real": fully_discharged,
                "blocker_state_transition_observed": blocker_movement,
                "branch_ruling_decisive": branch_ruling in [
                    "CLUSTER_FULLY_DISCHARGED_NO_BLOCKER_MOVE",
                    "CLUSTER_PRODUCTIVE_BLOCKER_MOVING",
                ],
            },
            "inputs": {
                "branch_ruling": branch_ruling,
                "allocation_decision": allocation_decision,
                "retention_role": retention_role,
                "rerun_policy": rerun_policy,
                "theorem_gap_delta": theorem_delta,
                "seam_integration_gap_delta": seam_delta,
                "global_row_success_count": global_row_success,
                "discharge_decision": discharge_decision.get("summary", {}).get("decision"),
                "trend_net_delta": int(trend.get("blocker_counts", {}).get("net_delta", 0) or 0),
                "progress_classification": ledger.get("progress_classification"),
            },
            "summary": {
                "all_criteria_satisfied": branch_ruling != "CLUSTER_EVALUATION_INCOMPLETE",
                "phase_status": "COMPLETE" if branch_ruling != "CLUSTER_EVALUATION_INCOMPLETE" else "INCOMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "branch_ruling": branch_ruling,
            "allocation_decision": allocation_decision,
            "retention_role": retention_role,
            "rerun_policy": rerun_policy,
            "blocker_facing_movement_observed": blocker_movement,
            "theorem_gap_delta": theorem_delta,
            "seam_integration_gap_delta": seam_delta,
            "global_row_success_count": global_row_success,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "gate_completion_tranche": _ptr(GATE_COMPLETION_TRANCHE_PATH),
            "discharge_tranche": _ptr(DISCHARGE_TRANCHE_PATH),
            "discharge_decision": _ptr(DISCHARGE_DECISION_PATH),
            "trend": _ptr(TREND_PATH),
            "ledger": _ptr(LEDGER_PATH),
        },
        "non_claim_boundary": "Repository-local proof-debt cluster branch ruling report; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate proof-debt cluster branch ruling report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "proof_debt_cluster_branch_ruling_report_20260411_v0.json",
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
        "proof_debt_cluster_branch_ruling_report: "
        f"branch_ruling={payload['summary']['branch_ruling']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
