from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_DECISION_REPORT_20260416_v0"

DEFAULT_PACKET_PATH = (
    REPO_ROOT / "formal" / "output" / "qm_stat_rl10_computational_analysis_packet_01_v0.json"
)
DEFAULT_EXECUTED_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "qm_stat_rl10_computational_analysis_packet_01_20260416_v0.json"
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
    findings = dict(executed_report.get("classificatory_findings", {}))
    executed_summary = dict(executed_report.get("summary", {}))
    criteria = dict(executed_report.get("criteria", {}))

    packet_boundary_preserved = (
        str(payload.get("status", "")).strip() == "RUN_BOUNDED_v0_NONCLAIM"
        and str(payload.get("decision", "")).strip() == "INCONCLUSIVE_v0"
        and bool(criteria.get("packet_decision_forced_inconclusive", False))
        and bool(criteria.get("restart_semantics_preserved", False))
    )
    stability_sufficient = str(findings.get("stability_classification", "")).strip() == "STABLE_v0"
    comparator_sensitivity_meaningful = (
        str(findings.get("comparator_classification", "")).strip() == "COMPARATOR_SENSITIVE_v0"
    )
    discriminator_signal_sufficient = (
        str(findings.get("discriminator_classification", "")).strip() == "DISCRIMINATIVE_v0"
    )
    no_material_triviality_evidence = str(findings.get("subordinate_disposition", "")).strip() != "PRUNE_v0"

    if (
        packet_boundary_preserved
        and stability_sufficient
        and comparator_sensitivity_meaningful
        and discriminator_signal_sufficient
        and no_material_triviality_evidence
    ):
        decision = "REFINE_v0"
        decision_basis = "SIGNAL_IS_MEANINGFUL_BUT_PACKET01_BOUNDARY_REMAINS_INCONCLUSIVE"
        next_action = "OPEN_AT_MOST_ONE_BOUNDED_PACKET01_REFINEMENT_UNDER_SAME_INCONCLUSIVE_CEILING"
    elif packet_boundary_preserved and (stability_sufficient or comparator_sensitivity_meaningful):
        decision = "RETAIN_v0"
        decision_basis = "BASELINE_IS_USEFUL_BUT_SINGLE_REFINEMENT_NOT_YET_JUSTIFIED"
        next_action = "FREEZE_PACKET01_BASELINE_AND_STOP_BEFORE_PACKET02"
    else:
        decision = "RETIRE_v0"
        decision_basis = "PACKET01_SIGNAL_TOO_WEAK_OR_ARTIFACT_DEPENDENT_FOR_FURTHER_USE"
        next_action = "RECORD_RETIREMENT_AND_STOP_WITH_NO_PACKET02"

    return {
        "schema_id": SCHEMA_ID,
        "report_id": "QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_DECISION_REPORT_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "packet_boundary_preserved": packet_boundary_preserved,
            "stability_sufficient": stability_sufficient,
            "comparator_sensitivity_meaningful": comparator_sensitivity_meaningful,
            "discriminator_signal_sufficient_for_one_refinement": discriminator_signal_sufficient,
            "no_material_triviality_or_artifact_dependence_evidence": no_material_triviality_evidence,
            "packet02_authorized": False,
            "restart_implication": False,
            "blocker_movement_claim": False,
        },
        "summary": {
            "decision": decision,
            "decision_basis": decision_basis,
            "next_action": next_action,
            "authorized_follow_on": "ONE_BOUNDED_PACKET01_REFINEMENT_ONLY" if decision == "REFINE_v0" else "NONE",
            "baseline_frozen": True,
            "packet_level_decision_remains": str(executed_summary.get("packet_decision", "INCONCLUSIVE_v0")).strip(),
        },
        "source_bundle": {
            "packet_artifact": _ptr(packet_path),
            "executed_report": _ptr(executed_report_path),
        },
        "non_claim_boundary": "Repository-local Packet-01 decision report only; no Packet-02 authorization, restart implication, blocker movement, lane reopen, or external-truth claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 computational-analysis Packet-01 decision report."
    )
    parser.add_argument("--packet", type=Path, default=DEFAULT_PACKET_PATH)
    parser.add_argument("--executed-report", type=Path, default=DEFAULT_EXECUTED_REPORT_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_computational_analysis_packet_01_decision_20260416_v0.json",
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
        "qm_stat_rl10_computational_analysis_packet_01_decision_report: "
        f"decision={payload['summary']['decision']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())