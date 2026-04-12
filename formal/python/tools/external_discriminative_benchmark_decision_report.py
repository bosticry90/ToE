from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "EXTERNAL_DISCRIMINATIVE_BENCHMARK_DECISION_20260411_v0"

DEFAULT_PACKET_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "external_discriminative_benchmark_packet_report_20260411_v0.json"
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
    packet_outcome = str(summary.get("packet_outcome", "INCONCLUSIVE_EXTERNAL_BENCHMARK_INPUTS_INCOMPLETE"))
    blocker_movement = bool(summary.get("blocker_facing_movement_observed", False))
    decisive_route_elimination = bool(summary.get("decisive_route_elimination_observed", False))
    material_route_credibility_gain = bool(summary.get("material_route_credibility_gain_observed", False))

    if blocker_movement:
        decision = "EXTERNAL_BENCHMARK_PROGRAM_PRODUCTIVE_BLOCKER_MOVING"
        next_action = "CONTINUE_EXTERNAL_BENCHMARK_PROGRAM_WITH_BLOCKER_REDUCTION_FOCUS"
    elif decisive_route_elimination or material_route_credibility_gain:
        decision = "EXTERNAL_BENCHMARK_PROGRAM_PRODUCTIVE_POSTURE_SHIFT"
        next_action = "RECLASSIFY_ROUTE_AND_EXECUTE_TARGETED_BLOCKER_ATTEMPT"
    elif packet_outcome.startswith("INCONCLUSIVE"):
        decision = "EXTERNAL_BENCHMARK_PROGRAM_INCONCLUSIVE"
        next_action = "REPAIR_BENCHMARK_INPUTS_AND_RERUN_ONE_BOUNDED_PACKET"
    else:
        decision = "EXTERNAL_BENCHMARK_PROGRAM_NONPRODUCTIVE"
        next_action = "INITIATE_FUNDAMENTAL_ATTACK_STRATEGY_RETHINK"

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
            "decisive_route_elimination_observed": decisive_route_elimination,
            "material_route_credibility_gain_observed": material_route_credibility_gain,
            "next_action": next_action,
            "next_attack_class_if_escalated": "FUNDAMENTAL_ATTACK_STRATEGY_RETHINK",
        },
        "source_bundle": {
            "packet_report": _ptr(packet_report_path),
        },
        "non_claim_boundary": "Repository-local external benchmark decision artifact; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate external discriminative benchmark decision report.")
    parser.add_argument("--packet-report", type=Path, default=DEFAULT_PACKET_REPORT_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "external_discriminative_benchmark_decision_20260411_v0.json",
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
        "external_discriminative_benchmark_decision_report: "
        f"decision={payload['summary']['decision']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
