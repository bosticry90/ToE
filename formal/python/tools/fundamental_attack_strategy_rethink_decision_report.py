from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "FUNDAMENTAL_ATTACK_STRATEGY_RETHINK_DECISION_20260411_v0"

DEFAULT_PACKET_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "fundamental_attack_strategy_rethink_packet_report_20260411_v0.json"
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

    packet_outcome = str(summary.get("packet_outcome", "INCONCLUSIVE_FAILURE_PATTERN_NOT_UNIFORM"))
    next_class = str(summary.get("selected_next_experimental_class", ""))

    if packet_outcome == "FUNDAMENTAL_RETHINK_COMPLETE_NEXT_CLASS_SELECTED" and next_class:
        decision = "FUNDAMENTAL_RETHINK_COMPLETE"
        next_action = f"EXECUTE_{next_class}_BOUNDED_PACKET"
    else:
        decision = "FUNDAMENTAL_RETHINK_INCOMPLETE"
        next_action = "REPAIR_RETHINK_PACKET_AND_RERUN_ONCE"

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
            "selected_next_experimental_class": next_class,
            "next_action": next_action,
        },
        "source_bundle": {
            "packet_report": _ptr(packet_report_path),
        },
        "non_claim_boundary": "Repository-local fundamental rethink decision artifact; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate fundamental attack strategy rethink decision report.")
    parser.add_argument("--packet-report", type=Path, default=DEFAULT_PACKET_REPORT_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "fundamental_attack_strategy_rethink_decision_20260411_v0.json",
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
        "fundamental_attack_strategy_rethink_decision_report: "
        f"decision={payload['summary']['decision']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
