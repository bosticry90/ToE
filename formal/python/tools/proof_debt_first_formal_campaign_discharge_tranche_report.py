from __future__ import annotations

import argparse
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "PROOF_DEBT_FIRST_FORMAL_CAMPAIGN_DISCHARGE_TRANCHE_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "PROOF_DEBT_FIRST_FORMAL_CAMPAIGN_DISCHARGE_TRANCHE_20260411_v0.json"
)
TREND_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_trend_window_20260410_v0.json"
ROW_TREND_PATH = REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_row_outcome_trend_20260411_v0.json"
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


def _run_gate(test_path: str) -> dict[str, Any]:
    fp = REPO_ROOT / test_path
    if not fp.exists():
        return {
            "test_path": test_path,
            "exists": False,
            "passed": False,
            "returncode": None,
            "stdout_tail": "",
            "stderr_tail": "missing_test_file",
        }

    cmd = [sys.executable, "-m", "pytest", test_path, "-q"]
    proc = subprocess.run(cmd, cwd=REPO_ROOT, capture_output=True, text=True)
    return {
        "test_path": test_path,
        "exists": True,
        "passed": proc.returncode == 0,
        "returncode": proc.returncode,
        "stdout_tail": "\n".join(proc.stdout.splitlines()[-10:]),
        "stderr_tail": "\n".join(proc.stderr.splitlines()[-10:]),
    }


def _object_discharged(results: list[dict[str, Any]]) -> bool:
    return len(results) > 0 and all(bool(r.get("passed", False)) for r in results)


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    trend = _read_json(TREND_PATH)
    row_trend = _read_json(ROW_TREND_PATH)
    ledger = _read_json(LEDGER_PATH)

    targets = declaration.get("debt_object_execution_targets", [])
    object_exec: list[dict[str, Any]] = []

    for obj in targets if isinstance(targets, list) else []:
        witness_tests = obj.get("witness_or_trace_required", [])
        test_results = [_run_gate(str(t)) for t in witness_tests] if isinstance(witness_tests, list) else []
        discharged = _object_discharged(test_results)
        object_exec.append(
            {
                "debt_id": obj.get("debt_id"),
                "current_unresolved_condition": obj.get("current_unresolved_condition"),
                "target_discharged_condition": obj.get("target_discharged_condition"),
                "artifact_or_theorem_surface": obj.get("artifact_or_theorem_surface"),
                "witness_or_trace_required": witness_tests,
                "blocker_link": obj.get("blocker_link"),
                "success_token_emitted": obj.get("success_token") if discharged else None,
                "fail_token_emitted": None if discharged else obj.get("fail_token"),
                "discharged": discharged,
                "gate_results": test_results,
            }
        )

    any_object_discharged = any(bool(o.get("discharged", False)) for o in object_exec)

    prior = trend.get("blocker_counts", {}).get("prior", {})
    current = trend.get("blocker_counts", {}).get("current", {})
    theorem_prior = int(prior.get("THEOREM_GAP", 0) or 0)
    theorem_current = int(current.get("THEOREM_GAP", theorem_prior) or theorem_prior)
    theorem_delta = theorem_current - theorem_prior
    seam_prior = int(prior.get("SEAM_INTEGRATION_GAP", 0) or 0)
    seam_current = int(current.get("SEAM_INTEGRATION_GAP", seam_prior) or seam_prior)
    seam_delta = seam_current - seam_prior

    row_counts = row_trend.get("objective_quality", {}).get("inputs", {}).get("row_outcome_counts", {})
    global_row_success = sum(int((v or {}).get("success", 0) or 0) for v in row_counts.values()) if isinstance(row_counts, dict) else 0

    blocker_state_moved = theorem_delta < 0 or seam_delta < 0 or global_row_success > 0
    formal_gap_closed_tied_to_blocker = any_object_discharged

    if any_object_discharged and blocker_state_moved:
        tranche_state = "PROOF_DEBT_DISCHARGE_SUCCESS_BLOCKER_MOVED"
    elif any_object_discharged and not blocker_state_moved:
        tranche_state = "PROOF_DEBT_DISCHARGE_PARTIAL_FORMAL_PROGRESS_NO_BLOCKER_MOVE"
    else:
        tranche_state = "PROOF_DEBT_DISCHARGE_FAILED_NO_FORMAL_CLOSURE"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "attack_class": declaration.get("attack_class"),
        "tranche_id": declaration.get("tranche_id"),
        "cluster_id": declaration.get("cluster_id"),
        "criteria": {
            "debt_object_targets_present": len(object_exec) > 0,
            "gate_execution_materialized": True,
            "cluster_level_state_emitted": tranche_state != "",
            "blocker_transition_criteria_applied": True,
        },
        "objective_quality": {
            "criteria": {
                "blocker_facing_movement_observed": blocker_state_moved,
                "formal_gap_closed_tied_to_blocker": formal_gap_closed_tied_to_blocker,
                "route_falsification_of_blocker_removal_path": False,
            },
            "inputs": {
                "tranche_state": tranche_state,
                "debt_object_execution": object_exec,
                "any_object_discharged": any_object_discharged,
                "theorem_gap_prior": theorem_prior,
                "theorem_gap_current": theorem_current,
                "theorem_gap_delta": theorem_delta,
                "seam_integration_gap_prior": seam_prior,
                "seam_integration_gap_current": seam_current,
                "seam_integration_gap_delta": seam_delta,
                "global_row_success_count": global_row_success,
                "progress_classification": ledger.get("progress_classification"),
            },
            "summary": {
                "all_criteria_satisfied": any_object_discharged,
                "phase_status": "COMPLETE",
                "next_action": (
                    "RECOMPUTE_BLOCKER_STATE_AND_DECIDE_CONTINUE_OR_REPRIORITIZE_CLUSTER"
                    if any_object_discharged
                    else "REPRIORITIZE_PROOF_DEBT_CLUSTER_OR_FIX_MISSING_GATES"
                ),
            },
        },
        "summary": {
            "tranche_state": tranche_state,
            "debt_object_count": len(object_exec),
            "any_object_discharged": any_object_discharged,
            "blocker_facing_movement_observed": blocker_state_moved,
            "formal_gap_closed_tied_to_blocker": formal_gap_closed_tied_to_blocker,
            "route_falsification_of_blocker_removal_path": False,
            "theorem_gap_delta": theorem_delta,
            "seam_integration_gap_delta": seam_delta,
            "global_row_success_count": global_row_success,
            "next_action": (
                "RECOMPUTE_BLOCKER_STATE_AND_DECIDE_CONTINUE_OR_REPRIORITIZE_CLUSTER"
                if any_object_discharged
                else "REPRIORITIZE_PROOF_DEBT_CLUSTER_OR_FIX_MISSING_GATES"
            ),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "trend": _ptr(TREND_PATH),
            "row_outcome_trend": _ptr(ROW_TREND_PATH),
            "ledger": _ptr(LEDGER_PATH),
        },
        "non_claim_boundary": "Repository-local proof-debt-first discharge tranche report; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate proof-debt-first discharge tranche report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "proof_debt_first_formal_campaign_discharge_tranche_report_20260411_v0.json",
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
        "proof_debt_first_formal_campaign_discharge_tranche_report: "
        f"tranche_state={payload['summary']['tranche_state']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
