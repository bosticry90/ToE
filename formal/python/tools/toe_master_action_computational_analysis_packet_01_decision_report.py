from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_DECISION_REPORT_20260417_v0"

DEFAULT_PACKET_PATH = REPO_ROOT / "formal" / "output" / "toe_master_action_computational_analysis_packet_01_v0.json"
DEFAULT_EXECUTED_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "toe_master_action_computational_analysis_packet_01_20260417_v0.json"
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


def build_report(*, packet_path: Path, executed_report_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    packet = _read_json(packet_path)
    executed_report = _read_json(executed_report_path)

    payload = dict(packet.get("payload", {}))
    criteria = dict(executed_report.get("criteria", {}))
    numeric_summary = dict(executed_report.get("numeric_summary", {}))
    findings = dict(executed_report.get("classificatory_findings", {}))
    subordinate_disposition = str(findings.get("subordinate_disposition", "")).strip()

    packet_boundary_preserved = (
        str(payload.get("status", "")).strip() == "RUN_BOUNDED_v0_NONCLAIM"
        and str(payload.get("decision", "")).strip() == "INCONCLUSIVE_v0"
        and bool(criteria.get("packet_status_bound_nonclaim", False))
        and bool(criteria.get("refinement_ceiling_preserved", False))
    )
    operator_signal_sufficient = bool(criteria.get("operator_stability_pass", False))
    residual_signal_sufficient = bool(criteria.get("residual_consistency_pass", False))
    regime_signal_sufficient = bool(criteria.get("regime_limit_sensitivity_pass", False))
    spectral_radius = float(numeric_summary.get("spectral_radius", 9.9))
    regime_span = float(numeric_summary.get("regime_limit_residual_span", 9.9))

    if (
        packet_boundary_preserved
        and operator_signal_sufficient
        and residual_signal_sufficient
        and regime_signal_sufficient
        and subordinate_disposition == "REFINE_CANDIDATE_v0"
        and spectral_radius < 1.0
        and regime_span >= 0.010
    ):
        decision = "REFINE_v0"
        decision_basis = "JOINT_OPERATOR_RESIDUAL_REGIME_SIGNAL_SUPPORTS_ONE_LOCAL_REFINEMENT"
        next_action = "AUTHORIZE_AT_MOST_ONE_LOCAL_PACKET01_REFINEMENT_WITH_SAME_OPERATOR_FAMILY"
    elif packet_boundary_preserved and subordinate_disposition == "RETAIN_CANDIDATE_v0":
        decision = "RETAIN_v0"
        decision_basis = "BASELINE_IS_COHERENT_BUT_ONE_REFINEMENT_IS_NOT_YET_JUSTIFIED"
        next_action = "FREEZE_PACKET01_BASELINE_AND_STOP_WITH_NO_PACKET02"
    elif packet_boundary_preserved and subordinate_disposition == "RETIRE_CANDIDATE_v0":
        decision = "RETIRE_v0"
        decision_basis = "PACKET01_IS_NONPRODUCTIVE_UNDER_DECLARED_BOUNDED_ASSUMPTIONS"
        next_action = "RECORD_RETIREMENT_AND_STOP_WITH_NO_PACKET02"
    else:
        decision = "INCONCLUSIVE_v0"
        decision_basis = "BOUNDARY_REACHED_WITHOUT_STRONG_ENOUGH_LOCAL_DECISION_SIGNAL"
        next_action = "STOP_AT_PACKET01_WITH_NO_PACKET02"

    return {
        "schema_id": SCHEMA_ID,
        "report_id": "TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_DECISION_REPORT_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "packet_boundary_preserved": packet_boundary_preserved,
            "operator_signal_sufficient": operator_signal_sufficient,
            "residual_signal_sufficient": residual_signal_sufficient,
            "regime_signal_sufficient": regime_signal_sufficient,
            "packet02_authorized": False,
            "gpu_backend_authorized": False,
            "lane_reopen_implication": False,
            "blocker_movement_claim": False,
        },
        "summary": {
            "decision": decision,
            "decision_basis": decision_basis,
            "next_action": next_action,
            "authorized_follow_on": "ONE_LOCAL_PACKET01_REFINEMENT_ONLY" if decision == "REFINE_v0" else "NONE",
            "packet_level_decision_remains": "INCONCLUSIVE_v0",
        },
        "source_bundle": {
            "packet_artifact": _ptr(packet_path),
            "executed_report": _ptr(executed_report_path),
        },
        "non_claim_boundary": "Repository-local master-action Packet-01 decision report only; no Packet-02 authorization, no GPU migration, no lane reopen, no blocker movement, and no external-truth claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the ToE master-action Packet-01 decision report.")
    parser.add_argument("--packet", type=Path, default=DEFAULT_PACKET_PATH)
    parser.add_argument("--executed-report", type=Path, default=DEFAULT_EXECUTED_REPORT_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "toe_master_action_computational_analysis_packet_01_decision_20260417_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    packet_path = ns.packet if ns.packet.is_absolute() else (REPO_ROOT / ns.packet)
    executed_report_path = ns.executed_report if ns.executed_report.is_absolute() else (REPO_ROOT / ns.executed_report)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_report(packet_path=packet_path, executed_report_path=executed_report_path, captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "toe_master_action_computational_analysis_packet_01_decision_report: "
        f"decision={payload['summary']['decision']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())