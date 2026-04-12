from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SIMULATION_FIRST_FALSIFICATION_CAMPAIGN_DECISION_20260411_v2"

DEFAULT_PACKET_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "simulation_first_falsification_packet_report_20260411_v2.json"
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

    packet_outcome = str(packet.get("summary", {}).get("packet_outcome", "INCONCLUSIVE_INSUFFICIENT_ROWS"))
    scientific_state_change = bool(packet.get("summary", {}).get("scientific_state_change_observed", False))
    usable_boundary_mapped = bool(packet.get("summary", {}).get("usable_boundary_mapped", False))
    blocker_facing_movement = bool(packet.get("summary", {}).get("blocker_facing_movement_observed", False))

    if blocker_facing_movement:
        decision = "SIMULATION_FIRST_CAMPAIGN_BLOCKER_MOVING"
        next_action = "CONTINUE_SIMULATION_FIRST_WITH_BLOCKER_REDUCTION_FOCUS"
    elif scientific_state_change and usable_boundary_mapped:
        decision = "SIMULATION_FIRST_CAMPAIGN_PRODUCTIVE_BOUNDARY_SHARPENED"
        next_action = "CONTINUE_SIMULATION_FIRST_WITH_REGIME_CONDITIONED_BLOCKER_ATTEMPT"
    elif scientific_state_change:
        decision = "SIMULATION_FIRST_CAMPAIGN_PARTIALLY_PRODUCTIVE"
        next_action = "RUN_ONE_MORE_BOUNDED_PACKET_THEN_REEVALUATE"
    else:
        decision = "SIMULATION_FIRST_CAMPAIGN_NONPRODUCTIVE"
        next_action = "ESCALATE_TO_NEXT_ATTACK_CLASS_BROADER_SEAM_PACKAGE_REDESIGN"

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
            "scientific_state_change_observed": scientific_state_change,
            "usable_boundary_mapped": usable_boundary_mapped,
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
    parser = argparse.ArgumentParser(description="Generate simulation-first falsification campaign v2 decision report.")
    parser.add_argument("--packet-report", type=Path, default=DEFAULT_PACKET_REPORT_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "simulation_first_falsification_campaign_decision_20260411_v2.json",
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
        "simulation_first_falsification_campaign_decision_v2_report: "
        f"decision={payload['summary']['decision']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
