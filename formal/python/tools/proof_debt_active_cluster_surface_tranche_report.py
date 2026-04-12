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
SCHEMA_ID = "PROOF_DEBT_ACTIVE_CLUSTER_SURFACE_TRANCHE_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PROOF_DEBT_ACTIVE_CLUSTER_SURFACE_TRANCHE_MATH_PD_C05_BURNDOWN_20260411_v0.json"
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


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = declaration.get("required_inputs", {})

    focus_path = REPO_ROOT / str(required_inputs.get("focus_report", ""))
    packet_path = REPO_ROOT / str(required_inputs.get("packet_report", ""))
    discharge_path = REPO_ROOT / str(required_inputs.get("discharge_tranche_report", ""))
    trend_path = REPO_ROOT / str(required_inputs.get("trend_pointer", ""))
    row_trend_path = REPO_ROOT / str(required_inputs.get("row_outcome_trend_pointer", ""))
    ledger_path = REPO_ROOT / str(required_inputs.get("ledger_pointer", ""))

    focus = _read_json(focus_path)
    packet = _read_json(packet_path)
    discharge = _read_json(discharge_path)
    trend = _read_json(trend_path)
    row_trend = _read_json(row_trend_path)
    ledger = _read_json(ledger_path)

    target_surface = declaration.get("target_surface", {})
    target_surface_id = str(target_surface.get("surface_id", ""))
    target_surface_path = str(target_surface.get("surface_path", ""))

    focus_selected_surface_id = str(focus.get("summary", {}).get("selected_surface_id", ""))
    focus_selected_surface_path = str(focus.get("summary", {}).get("selected_surface_path", ""))

    gate_result = _run_gate(target_surface_path)

    theorem_gap_delta = int(discharge.get("summary", {}).get("theorem_gap_delta", 0) or 0)
    seam_gap_delta = int(discharge.get("summary", {}).get("seam_integration_gap_delta", 0) or 0)
    global_row_success_count = int(discharge.get("summary", {}).get("global_row_success_count", 0) or 0)
    progress_classification = str(ledger.get("progress_classification", ""))

    movement_signals = {
        "theorem_gap_state_changed": theorem_gap_delta < 0,
        "seam_integration_state_changed": seam_gap_delta < 0,
        "global_row_success_state_changed": global_row_success_count > 0,
        "blocker_state_token_changed": progress_classification == "PROGRESS",
    }
    movement_observed = any(movement_signals.values())

    if gate_result.get("passed", False) and movement_observed:
        tranche_outcome = "SURFACE_EXECUTED_WITH_BLOCKER_MOVEMENT"
    elif gate_result.get("passed", False) and (not movement_observed):
        tranche_outcome = "SURFACE_EXECUTED_NO_BLOCKER_MOVEMENT"
    else:
        tranche_outcome = "SURFACE_EXECUTION_FAILED"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "cluster_id": declaration.get("cluster_id"),
        "tranche_id": declaration.get("tranche_id"),
        "criteria": {
            "focus_surface_matches_tranche_surface": (
                focus_selected_surface_id == target_surface_id
                and focus_selected_surface_path == target_surface_path
            ),
            "surface_gate_execution_materialized": True,
            "surface_gate_passed": bool(gate_result.get("passed", False)),
            "active_cluster_matches_packet": (
                str(declaration.get("cluster_id", ""))
                == str(packet.get("summary", {}).get("selected_cluster_id", ""))
            ),
            "movement_signals_materialized": True,
        },
        "objective_quality": {
            "criteria": {
                "surface_executed": bool(gate_result.get("passed", False)),
                "theorem_gap_state_change_observed": movement_signals["theorem_gap_state_changed"],
                "seam_integration_state_change_observed": movement_signals["seam_integration_state_changed"],
                "global_row_success_state_change_observed": movement_signals["global_row_success_state_changed"],
                "blocker_state_token_change_observed": movement_signals["blocker_state_token_changed"],
            },
            "inputs": {
                "target_surface_id": target_surface_id,
                "target_surface_path": target_surface_path,
                "focus_selected_surface_id": focus_selected_surface_id,
                "focus_selected_surface_path": focus_selected_surface_path,
                "gate_result": gate_result,
                "theorem_gap_delta": theorem_gap_delta,
                "seam_integration_gap_delta": seam_gap_delta,
                "global_row_success_count": global_row_success_count,
                "progress_classification": progress_classification,
                "trend_net_delta": int(trend.get("blocker_counts", {}).get("net_delta", 0) or 0),
                "row_outcome_counts": row_trend.get("objective_quality", {}).get("inputs", {}).get("row_outcome_counts", {}),
            },
            "summary": {
                "all_criteria_satisfied": bool(gate_result.get("passed", False)),
                "phase_status": "COMPLETE" if bool(gate_result.get("passed", False)) else "INCOMPLETE",
                "next_action": (
                    "CONTINUE_SURFACE_CHAIN_WITH_BLOCKER_STATE_RECOMPUTE"
                    if movement_observed
                    else "ESCALATE_WITHIN_ACTIVE_CLUSTER_SURFACE_CHAIN"
                ),
            },
        },
        "summary": {
            "tranche_outcome": tranche_outcome,
            "target_surface_id": target_surface_id,
            "target_surface_path": target_surface_path,
            "surface_gate_passed": bool(gate_result.get("passed", False)),
            "movement_signals": movement_signals,
            "next_action": (
                "CONTINUE_SURFACE_CHAIN_WITH_BLOCKER_STATE_RECOMPUTE"
                if movement_observed
                else "PREPARE_NEXT_ACTIVE_CLUSTER_SURFACE_BOUND"
            ),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "focus_report": _ptr(focus_path),
            "packet_report": _ptr(packet_path),
            "discharge_tranche_report": _ptr(discharge_path),
            "trend": _ptr(trend_path),
            "row_outcome_trend": _ptr(row_trend_path),
            "ledger": _ptr(ledger_path),
        },
        "non_claim_boundary": "Repository-local bounded active-surface tranche report; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate bounded active-cluster surface tranche report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "proof_debt_active_cluster_surface_tranche_report_20260411_v0.json",
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
        "proof_debt_active_cluster_surface_tranche_report: "
        f"tranche_outcome={payload['summary']['tranche_outcome']} "
        f"target_surface_id={payload['summary']['target_surface_id']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
