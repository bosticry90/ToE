from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "PROOF_DEBT_ACTIVE_CLUSTER_SURFACE_RULING_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PROOF_DEBT_ACTIVE_CLUSTER_SURFACE_RULING_MATH_PD_C05_BURNDOWN_GATE_20260411_v0.json"
)


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

    required_inputs = declaration.get("required_inputs", {})
    surface_tranche_report_path = REPO_ROOT / str(required_inputs.get("surface_tranche_report", ""))
    surface_tranche_report = _read_json(surface_tranche_report_path)

    target_surface = dict(declaration.get("target_surface", {}))
    target_surface_id = str(target_surface.get("surface_id", ""))
    target_surface_path = str(target_surface.get("surface_path", ""))

    tranche_summary = dict(surface_tranche_report.get("summary", {}))
    tranche_target_surface_id = str(tranche_summary.get("target_surface_id", ""))
    tranche_target_surface_path = str(tranche_summary.get("target_surface_path", ""))
    gate_passed = bool(tranche_summary.get("surface_gate_passed", False))
    movement_signals = dict(tranche_summary.get("movement_signals", {}))
    movement_observed = any(bool(value) for value in movement_signals.values())

    target_surface_matches = (
        target_surface_id == tranche_target_surface_id and target_surface_path == tranche_target_surface_path
    )

    if target_surface_matches and gate_passed and not movement_observed:
        surface_ruling = "SURFACE_EXECUTED_VALID_NO_BLOCKER_MOVEMENT"
        allocation_decision = "DEPRIORITIZE_AS_IMMEDIATE_BLOCKER_FACING_NEXT_TRANCHE_SURFACE"
        retention_role = "LOCALLY_VALID_NON_MOVING_SUPPORT_SURFACE"
        rerun_policy = "EXCLUDE_FROM_IMMEDIATE_RESELECTION_UNDER_CURRENT_CRITERIA"
        exclude_from_immediate_reselection = True
        next_action = "ADVANCE_TO_NEXT_ACTIVE_CLUSTER_SURFACE_CANDIDATE"
    elif target_surface_matches and gate_passed and movement_observed:
        surface_ruling = "SURFACE_PRODUCTIVE_BLOCKER_MOVING"
        allocation_decision = "RETAIN_AS_PRODUCTIVE_BLOCKER_FACING_SURFACE"
        retention_role = "PRIMARY_BLOCKER_REDUCTION_SURFACE"
        rerun_policy = "ALLOW_SUCCESSOR_SURFACE_CHAIN_OR_RECOMPUTE"
        exclude_from_immediate_reselection = False
        next_action = "CONTINUE_PRODUCTIVE_ACTIVE_CLUSTER_SURFACE_CHAIN"
    else:
        surface_ruling = "SURFACE_RULING_INCOMPLETE"
        allocation_decision = "HOLD_SURFACE_RULING_PENDING_PRECONDITIONS"
        retention_role = "UNRESOLVED"
        rerun_policy = "RESTORE_PRECONDITIONS_AND_RERUN_ONCE"
        exclude_from_immediate_reselection = False
        next_action = "RESTORE_SURFACE_RULING_PRECONDITIONS"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "cluster_id": declaration.get("cluster_id"),
        "target_surface": target_surface,
        "criteria": {
            "surface_tranche_report_present": surface_tranche_report_path.exists(),
            "target_surface_matches_tranche_surface": target_surface_matches,
            "surface_executed": gate_passed,
            "blocker_movement_judged": bool(movement_signals),
            "surface_ruling_materialized": surface_ruling != "",
        },
        "objective_quality": {
            "criteria": {
                "locally_valid_surface_confirmed": gate_passed,
                "blocker_facing_movement_absent": not movement_observed,
                "immediate_reselection_excluded": exclude_from_immediate_reselection,
            },
            "inputs": {
                "surface_ruling": surface_ruling,
                "allocation_decision": allocation_decision,
                "retention_role": retention_role,
                "rerun_policy": rerun_policy,
                "tranche_outcome": tranche_summary.get("tranche_outcome"),
                "movement_signals": movement_signals,
            },
            "summary": {
                "all_criteria_satisfied": surface_ruling != "SURFACE_RULING_INCOMPLETE",
                "phase_status": "COMPLETE" if surface_ruling != "SURFACE_RULING_INCOMPLETE" else "INCOMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "surface_id": target_surface_id,
            "surface_path": target_surface_path,
            "surface_ruling": surface_ruling,
            "allocation_decision": allocation_decision,
            "retention_role": retention_role,
            "rerun_policy": rerun_policy,
            "gate_passed": gate_passed,
            "blocker_facing_movement_observed": movement_observed,
            "exclude_from_immediate_reselection": exclude_from_immediate_reselection,
            "deprioritized_as_immediate_blocker_facing_next_tranche_surface": exclude_from_immediate_reselection,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "surface_tranche_report": _ptr(surface_tranche_report_path),
        },
        "non_claim_boundary": "Repository-local active-cluster surface ruling report; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate active-cluster surface ruling report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "proof_debt_active_cluster_surface_ruling_math_pd_c05_burndown_gate_20260411_v0.json",
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
        "proof_debt_active_cluster_surface_ruling_report: "
        f"surface_ruling={payload['summary']['surface_ruling']} "
        f"surface_id={payload['summary']['surface_id']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
