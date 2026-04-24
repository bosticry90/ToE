from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "EM_U1_MICRO26_DOUBLE_DIVERGENCE_BINDING_THEOREM_CLOSEOUT_DECISION_20260417_v0"
DEFAULT_OUT_RELATIVE_PATH = (
    "formal/output/reports/em_u1_micro26_double_divergence_binding_theorem_closeout_decision_20260417_v0.json"
)

DEFAULT_EXECUTION_SURFACE_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "em_u1_micro26_double_divergence_binding_theorem_closure_attempt_execution_surface_v0.json"
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


def build_report(*, execution_surface_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    execution_surface = _read_json(execution_surface_path)
    checks = dict(execution_surface.get("checks", {}))

    execution_surface_green = (
        str(execution_surface.get("execution_surface_status", "")).strip() == "bounded_execution_surface_pinned"
        and execution_surface.get("missing", []) == []
        and all(bool(value) for value in checks.values())
    )
    packet01_frozen = str(execution_surface.get("packet_01_scope_status", "")).strip() == "frozen_out_of_scope"
    verification_green = str(execution_surface.get("verification_tranche_status", "")).strip() == "complete_green"
    bounded_scope_preserved = str(execution_surface.get("bounded_scope", "")).strip() == "cycle26_only_attempt_only"
    attempt_only_preserved = str(execution_surface.get("adjudication", "")).strip().endswith("NOT_YET_DISCHARGED")
    direct_prerequisite_pinned = (
        str(execution_surface.get("direct_prerequisites", {}).get("cycle25_kernel_artifact", "")).strip()
        == "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_25_DOUBLE_DIVERGENCE_THEOREM_CLOSURE_ATTEMPT_v0.md"
    )

    if execution_surface_green and packet01_frozen and verification_green and bounded_scope_preserved and attempt_only_preserved:
        decision = "RETAIN_MICRO26_BOUNDED_ENDPOINT_v0"
        handoff_status = "READY_FOR_NEXT_AUTHORIZED_LANE_ONLY_v0"
        next_action = "STOP_AT_MICRO26_CLOSEOUT_PENDING_EXPLICIT_MICRO27_AUTHORIZATION"
        basis = "EXECUTION_SURFACE_GREEN_AND_BOUNDARY_GUARDS_PRESERVED"
    elif bounded_scope_preserved and attempt_only_preserved:
        decision = "HOLD_MICRO26_REPAIR_REQUIRED_v0"
        handoff_status = "NOT_READY_FOR_HANDOFF_v0"
        next_action = "REPAIR_MICRO26_EXECUTION_OR_BOUNDARY_DRIFT"
        basis = "EXECUTION_SURFACE_OR_SCOPE_CHECK_FAILED"
    else:
        decision = "HOLD_MICRO26_BOUNDARY_REVIEW_v0"
        handoff_status = "NOT_READY_FOR_HANDOFF_v0"
        next_action = "STOP_AND_REVIEW_BOUNDARY_DRIFT_BEFORE_ANY_SUCCESSOR_LANE"
        basis = "BOUNDED_SCOPE_OR_ATTEMPT_ONLY_POSTURE_NOT_PRESERVED"

    return {
        "schema_id": SCHEMA_ID,
        "report_id": "EM_U1_MICRO26_DOUBLE_DIVERGENCE_BINDING_THEOREM_CLOSEOUT_DECISION_REPORT_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "execution_surface_green": execution_surface_green,
            "packet01_frozen_out_of_scope": packet01_frozen,
            "verification_tranche_green": verification_green,
            "bounded_scope_preserved": bounded_scope_preserved,
            "attempt_only_preserved": attempt_only_preserved,
            "direct_prerequisite_pinned": direct_prerequisite_pinned,
            "bounded_closeout_decision_materialized": True,
        },
        "summary": {
            "decision": decision,
            "decision_basis": basis,
            "handoff_status": handoff_status,
            "next_action": next_action,
            "authorized_follow_on": "MICRO27_ONLY_IF_EXPLICITLY_AUTHORIZED",
            "packet01_reopened": False,
        },
        "source_bundle": {
            "execution_surface_report": _ptr(execution_surface_path),
            "target_doc": "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_26_DOUBLE_DIVERGENCE_BINDING_THEOREM_CLOSURE_ATTEMPT_v0.md",
            "gate": "formal/python/tests/test_em_u1_micro26_double_divergence_binding_theorem_closure_attempt.py",
        },
        "non_claim_boundary": "Repository-local EM U1 Micro-26 closeout decision report only; bounded attempt-only family status, no Micro-27 activation, no Packet-01 reopen, no theorem discharge, and no external-truth claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the EM U1 Micro-26 closeout decision report.")
    parser.add_argument("--execution-surface", type=Path, default=DEFAULT_EXECUTION_SURFACE_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / DEFAULT_OUT_RELATIVE_PATH,
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    execution_surface_path = ns.execution_surface if ns.execution_surface.is_absolute() else (REPO_ROOT / ns.execution_surface)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_report(execution_surface_path=execution_surface_path, captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "em_u1_micro26_double_divergence_binding_theorem_closeout_decision_report: "
        f"decision={payload['summary']['decision']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())