from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SIMULATION_FIRST_FALSIFICATION_CAMPAIGN_DECISION_20260411_v3"

DEFAULT_PACKET_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "simulation_first_falsification_packet_report_20260411_v3.json"
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


def build_report(*, packet_report_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    packet = _read_json(packet_report_path)

    summary = packet.get("summary", {})
    packet_outcome = str(summary.get("packet_outcome", "INCONCLUSIVE_REGIME_PRECONDITION_NOT_MET"))
    blocker_facing_movement = bool(summary.get("blocker_facing_movement_observed", False))
    regime_precondition_met = bool(summary.get("regime_precondition_met", False))

    if blocker_facing_movement:
        decision = "SIMULATION_FIRST_CAMPAIGN_BLOCKER_MOVING_FROM_CONDITION_B_REGIME"
        next_action = "CONTINUE_REGIME_CONDITIONED_BLOCKER_REDUCTION"
    elif regime_precondition_met:
        decision = "SIMULATION_FIRST_CAMPAIGN_SCIENTIFICALLY_SHARP_OPERATIONALLY_NONPRODUCTIVE"
        next_action = "ESCALATE_TO_NEXT_ATTACK_CLASS_BROADER_SEAM_PACKAGE_REDESIGN"
    else:
        decision = "SIMULATION_FIRST_CAMPAIGN_INCONCLUSIVE_RETRY_REGIME_PACKET"
        next_action = "REPAIR_INPUTS_AND_RERUN_ONE_BOUNDED_REGIME_PACKET"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "packet_report_present": packet_report_path.exists(),
            "packet_outcome_materialized": packet_outcome != "",
            "bounded_campaign_decision_materialized": True,
        },
        "summary": {
            "decision": decision,
            "packet_outcome": packet_outcome,
            "regime_precondition_met": regime_precondition_met,
            "blocker_facing_movement_observed": blocker_facing_movement,
            "next_action": next_action,
            "next_attack_class_if_escalated": "BROADER_SEAM_PACKAGE_REDESIGN",
        },
        "source_bundle": {
            "packet_report": _ptr(packet_report_path),
        },
        "non_claim_boundary": "Repository-local simulation-first campaign decision artifact; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate simulation-first falsification campaign v3 decision report.")
    parser.add_argument("--packet-report", type=Path, default=DEFAULT_PACKET_REPORT_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "simulation_first_falsification_campaign_decision_20260411_v3.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    packet_report_path = ns.packet_report if ns.packet_report.is_absolute() else (REPO_ROOT / ns.packet_report)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(packet_report_path=packet_report_path, captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "simulation_first_falsification_campaign_decision_v3_report: "
        f"decision={payload['summary']['decision']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
