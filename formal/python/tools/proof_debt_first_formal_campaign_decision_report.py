from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "PROOF_DEBT_FIRST_FORMAL_CAMPAIGN_DECISION_20260411_v0"

DEFAULT_PACKET_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "proof_debt_first_formal_campaign_packet_report_20260411_v0.json"
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

    packet_outcome = str(summary.get("packet_outcome", "INCONCLUSIVE_PACKET_DEFINITION_OR_INPUTS_INCOMPLETE"))
    blocker_movement = bool(summary.get("blocker_facing_movement_observed", False))
    formal_gap_closed = bool(summary.get("formal_gap_closed_tied_to_blocker", False))
    route_falsification = bool(summary.get("route_falsification_of_blocker_removal_path", False))

    if blocker_movement or formal_gap_closed:
        decision = "PROOF_DEBT_FIRST_CAMPAIGN_PRODUCTIVE"
        next_action = "CONTINUE_PROOF_DEBT_FIRST_WITH_NEXT_BOUNDED_DISCHARGE_PACKET"
    elif route_falsification:
        decision = "PROOF_DEBT_FIRST_CAMPAIGN_PRODUCTIVE_VIA_PATH_FALSIFICATION"
        next_action = "RECLASSIFY_BLOCKER_REMOVAL_PATH_AND_SELECT_NEXT_BOUNDED_FORMAL_TARGET"
    elif packet_outcome == "PROOF_DEBT_PACKET_READY_NO_BLOCKER_MOVEMENT_YET":
        decision = "PROOF_DEBT_FIRST_CAMPAIGN_LAUNCHED_AWAITING_DISCHARGE_EXECUTION"
        next_action = "EXECUTE_BOUNDED_PROOF_DEBT_DISCHARGE_TRANCHE"
    elif packet_outcome.startswith("INCONCLUSIVE"):
        decision = "PROOF_DEBT_FIRST_CAMPAIGN_INCONCLUSIVE"
        next_action = "REPAIR_PACKET_AND_RERUN_ONCE"
    else:
        decision = "PROOF_DEBT_FIRST_CAMPAIGN_NONPRODUCTIVE"
        next_action = "ESCALATE_TO_ALTERNATE_FOUNDATIONAL_STRESS_TEST"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "packet_report_present": packet_report_path.exists(),
            "packet_outcome_materialized": packet_outcome != "",
            "bounded_decision_materialized": True,
        },
        "summary": {
            "decision": decision,
            "packet_outcome": packet_outcome,
            "blocker_facing_movement_observed": blocker_movement,
            "formal_gap_closed_tied_to_blocker": formal_gap_closed,
            "route_falsification_of_blocker_removal_path": route_falsification,
            "next_action": next_action,
        },
        "source_bundle": {
            "packet_report": _ptr(packet_report_path),
        },
        "non_claim_boundary": "Repository-local proof-debt-first campaign decision artifact; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate proof-debt-first formal campaign decision report.")
    parser.add_argument("--packet-report", type=Path, default=DEFAULT_PACKET_REPORT_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "proof_debt_first_formal_campaign_decision_20260411_v0.json",
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
        "proof_debt_first_formal_campaign_decision_report: "
        f"decision={payload['summary']['decision']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
