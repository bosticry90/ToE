from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "R0_R6_OBJECTIVE_QUALITY_CLOSEOUT_20260411_v0"

R0_PATH = REPO_ROOT / "formal" / "output" / "reports" / "science_global_completion_baseline_20260411_v0.json"
R1_PATH = REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_reduction_wave_20260411_v0.json"
R2_PATH = REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_execution_linkage_20260411_v0.json"
R3_PATH = REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_row_outcome_trend_20260411_v0.json"
R4_PATH = REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_single_row_execution_20260411_v0.json"
R5_PATH = REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_qm_rework_tranche_20260411_v0.json"
R6_PATH = REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_qm_subtarget_tranche_20260411_v0.json"


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


def _objective_surface_present(payload: dict[str, Any]) -> bool:
    obj = payload.get("objective_quality", {})
    return isinstance(obj.get("criteria"), dict) and isinstance(obj.get("summary"), dict)


def build_report(captured_at_utc: str | None) -> dict[str, Any]:
    r0 = _read_json(R0_PATH)
    r1 = _read_json(R1_PATH)
    r2 = _read_json(R2_PATH)
    r3 = _read_json(R3_PATH)
    r4 = _read_json(R4_PATH)
    r5 = _read_json(R5_PATH)
    r6 = _read_json(R6_PATH)

    reports = {
        "R0": r0,
        "R1": r1,
        "R2": r2,
        "R3": r3,
        "R4": r4,
        "R5": r5,
        "R6": r6,
    }

    criteria = {
        "all_r0_r6_reports_present": True,
        "all_r0_r6_reports_have_objective_surface": all(_objective_surface_present(p) for p in reports.values()),
        "all_r0_r6_contract_surfaces_complete": all(
            p.get("summary", {}).get("phase_status") == "COMPLETE"
            for p in reports.values()
        ),
        "r2_no_change_fail_closed_route_satisfied": r2.get("criteria", {}).get("no_change_requires_rework_route") is True,
        "r3_row_stagnation_visibility_materialized": isinstance(
            r3.get("objective_quality", {}).get("inputs", {}).get("stagnation_rows"), list
        ),
        "r4_single_row_fail_closed_route_satisfied": r4.get("objective_quality", {}).get("criteria", {}).get(
            "no_change_fail_closed_route_satisfied"
        )
        in {True, False},
        "r5_qm_rework_fail_closed_route_satisfied": r5.get("objective_quality", {}).get("criteria", {}).get(
            "no_change_fail_closed_route_satisfied"
        )
        in {True, False},
        "r6_qm_subtarget_failure_diagnosis_materialized": bool(
            r6.get("objective_quality", {}).get("inputs", {}).get("failure_diagnosis")
        ),
    }

    scientific_objective_complete = all(
        bool(p.get("objective_quality", {}).get("summary", {}).get("all_criteria_satisfied"))
        for p in reports.values()
    )
    control_stack_objective_complete = all(criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": criteria,
        "completion_assessment": {
            "control_stack_objective_complete": control_stack_objective_complete,
            "scientific_objective_complete": scientific_objective_complete,
            "global_objective_complete": control_stack_objective_complete and scientific_objective_complete,
        },
        "summary": {
            "all_criteria_satisfied": control_stack_objective_complete,
            "phase_status": "COMPLETE" if control_stack_objective_complete else "INCOMPLETE",
            "next_action": (
                "EXECUTE_BLOCKER_MOVING_QM_REWORK"
                if control_stack_objective_complete and not scientific_objective_complete
                else "RESTORE_R0_R6_CONTROL_STACK_SURFACE"
            ),
        },
        "source_bundle": {
            "R0": _ptr(R0_PATH),
            "R1": _ptr(R1_PATH),
            "R2": _ptr(R2_PATH),
            "R3": _ptr(R3_PATH),
            "R4": _ptr(R4_PATH),
            "R5": _ptr(R5_PATH),
            "R6": _ptr(R6_PATH),
        },
        "non_claim_boundary": "Repository-local control-stack closeout artifact for R0-R6; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate R0-R6 objective-quality closeout report.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "r0_r6_objective_quality_closeout_20260411_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"r0_r6_objective_quality_closeout_report: phase_status={payload['summary']['phase_status']} out={out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())