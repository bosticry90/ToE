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
SCHEMA_ID = "PROOF_DEBT_EMU1_GATE_SURFACE_COMPLETION_TRANCHE_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "PROOF_DEBT_EMU1_GATE_SURFACE_COMPLETION_TRANCHE_20260411_v0.json"
)
DISCHARGE_DECL_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "PROOF_DEBT_FIRST_FORMAL_CAMPAIGN_DISCHARGE_TRANCHE_20260411_v0.json"
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


def _run_pytest(test_path: str) -> dict[str, Any]:
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
    discharge_decl = _read_json(DISCHARGE_DECL_PATH)

    gate_path = str(declaration.get("required_gate_surface", {}).get("path", ""))
    gate_result = _run_pytest(gate_path)

    discharge_targets = discharge_decl.get("debt_object_execution_targets", [])
    rerun_ready = any(
        isinstance(item, dict)
        and str(item.get("debt_id", "")) == "PD-INV-PHYS-EM-U1-MICRO21"
        and gate_path in (item.get("witness_or_trace_required", []) if isinstance(item.get("witness_or_trace_required", []), list) else [])
        for item in (discharge_targets if isinstance(discharge_targets, list) else [])
    )

    success = bool(gate_result.get("passed", False)) and rerun_ready

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "tranche_id": declaration.get("tranche_id"),
        "cluster_id": declaration.get("cluster_id"),
        "criteria": {
            "gate_surface_exists": bool(gate_result.get("exists", False)),
            "gate_surface_passes": bool(gate_result.get("passed", False)),
            "cluster_rerun_on_merits_is_wired": rerun_ready,
            "bounded_decision_materialized": True,
        },
        "objective_quality": {
            "criteria": {
                "success_condition_satisfied": success,
                "failure_condition_satisfied": not success,
            },
            "inputs": {
                "gate_result": gate_result,
                "rerun_ready": rerun_ready,
                "packet_outcome": (
                    "EMU1_GATE_SURFACE_COMPLETED_AND_RERUN_READY"
                    if success
                    else "EMU1_GATE_SURFACE_INSUFFICIENT_OR_UNWIRED"
                ),
            },
            "summary": {
                "all_criteria_satisfied": success,
                "phase_status": "COMPLETE",
                "next_action": (
                    "RERUN_CLUSTER_ONCE_ON_MERITS"
                    if success
                    else "REPRIORITIZE_CLUSTER_INSUFFICIENT_INFRASTRUCTURE_LEVERAGE"
                ),
            },
        },
        "summary": {
            "packet_outcome": (
                "EMU1_GATE_SURFACE_COMPLETED_AND_RERUN_READY"
                if success
                else "EMU1_GATE_SURFACE_INSUFFICIENT_OR_UNWIRED"
            ),
            "gate_surface_exists": bool(gate_result.get("exists", False)),
            "gate_surface_passes": bool(gate_result.get("passed", False)),
            "rerun_ready": rerun_ready,
            "next_action": (
                "RERUN_CLUSTER_ONCE_ON_MERITS"
                if success
                else "REPRIORITIZE_CLUSTER_INSUFFICIENT_INFRASTRUCTURE_LEVERAGE"
            ),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "discharge_declaration": _ptr(DISCHARGE_DECL_PATH),
        },
        "non_claim_boundary": "Repository-local EM-U1 gate-surface completion tranche report; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate EM-U1 gate-surface completion tranche report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "proof_debt_emu1_gate_surface_completion_tranche_report_20260411_v0.json",
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
        "proof_debt_emu1_gate_surface_completion_tranche_report: "
        f"packet_outcome={payload['summary']['packet_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
