from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "TOE_ENFORCED_EXECUTION_CLOSEOUT_20260411_v0"

PHASE_REPORTS = {
    "PHASE_A_PROGRAM_LOCK": REPO_ROOT / "formal" / "output" / "reports" / "toe_enforced_execution_program_20260411_v0.json",
    "PHASE_B_RUNTIME_MEASUREMENT_INTEGRITY": REPO_ROOT / "formal" / "output" / "reports" / "runtime_measurement_integrity_20260411_v0.json",
    "PHASE_C_PACKET41_SUCCESSOR_DECISION_ENFORCEMENT": REPO_ROOT / "formal" / "output" / "reports" / "packet41_successor_decision_enforcement_20260411_v0.json",
    "PHASE_D_GOVERNANCE_SINGLE_SOURCE_CONSOLIDATION": REPO_ROOT / "formal" / "output" / "reports" / "governance_single_source_consolidation_20260411_v0.json",
    "PHASE_E_SCALE_OBSERVABILITY_AND_COST_CONTROL": REPO_ROOT / "formal" / "output" / "reports" / "governance_scale_observability_20260411_v0.json",
    "PHASE_F_CROSS_PLATFORM_PARITY": REPO_ROOT / "formal" / "output" / "reports" / "governance_cross_platform_parity_20260411_v0.json",
}


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def build_report(captured_at_utc: str | None) -> dict[str, Any]:
    phase_status: dict[str, bool] = {}
    objective_phase_status: dict[str, bool] = {}
    pointers: dict[str, str] = {}

    for phase, path in PHASE_REPORTS.items():
        payload = _read_json(path)
        if phase == "PHASE_A_PROGRAM_LOCK":
            phase_status[phase] = payload.get("summary", {}).get("program_lock_active") is True
            objective_phase_status[phase] = phase_status[phase]
        else:
            phase_status[phase] = payload.get("summary", {}).get("phase_status") == "COMPLETE"
            objective_phase_status[phase] = payload.get("objective_quality", {}).get("summary", {}).get("phase_status") == "COMPLETE"
        pointers[phase] = str(path.relative_to(REPO_ROOT)).replace("\\", "/")

    # Phase G completion depends on all A-F completed.
    preclose_complete = all(phase_status.values())
    phase_status["PHASE_G_CLOSEOUT_AND_AUTHORITY_SYNC"] = preclose_complete
    preclose_objective_complete = all(objective_phase_status.values())
    objective_phase_status["PHASE_G_CLOSEOUT_AND_AUTHORITY_SYNC"] = preclose_objective_complete
    pointers["PHASE_G_CLOSEOUT_AND_AUTHORITY_SYNC"] = "formal/output/reports/toe_enforced_execution_closeout_20260411_v0.json"

    contract_complete = all(phase_status.values())
    objective_complete = all(objective_phase_status.values())

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "phase_completion": phase_status,
        "objective_phase_completion": objective_phase_status,
        "source_bundle": pointers,
        "summary": {
            "all_phases_complete": contract_complete,
            "closeout_status": "COMPLETE" if contract_complete else "INCOMPLETE",
            "objective_all_phases_complete": objective_complete,
            "objective_closeout_status": "COMPLETE" if objective_complete else "INCOMPLETE",
            "next_action": "MAINTENANCE_MODE" if contract_complete else "CONTINUE_PHASE_EXECUTION",
            "objective_next_action": (
                "MAINTENANCE_MODE"
                if objective_complete
                else "CONTINUE_OBJECTIVE_QUALITY_HARDENING"
            ),
        },
        "non_claim_boundary": "Repository-local execution closeout artifact; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate A-G enforced execution closeout report.")
    parser.add_argument("--out", type=Path, default=REPO_ROOT / "formal" / "output" / "reports" / "toe_enforced_execution_closeout_20260411_v0.json")
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"toe_enforced_execution_closeout: closeout_status={payload['summary']['closeout_status']} out={out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
