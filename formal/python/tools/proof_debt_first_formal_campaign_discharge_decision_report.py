from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "PROOF_DEBT_FIRST_FORMAL_CAMPAIGN_DISCHARGE_DECISION_20260411_v0"

DEFAULT_TRANCHE_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "proof_debt_first_formal_campaign_discharge_tranche_report_20260411_v0.json"
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


def build_report(*, tranche_report_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    tranche = _read_json(tranche_report_path)
    summary = tranche.get("summary", {})

    tranche_state = str(summary.get("tranche_state", "PROOF_DEBT_DISCHARGE_FAILED_NO_FORMAL_CLOSURE"))

    if tranche_state == "PROOF_DEBT_DISCHARGE_SUCCESS_BLOCKER_MOVED":
        decision = "PROOF_DEBT_DISCHARGE_PRODUCTIVE_BLOCKER_MOVING"
        next_action = "CONTINUE_BOUNDED_PROOF_DEBT_DISCHARGE_ON_SAME_CLUSTER_UNTIL_DELTA_STALL"
    elif tranche_state == "PROOF_DEBT_DISCHARGE_PARTIAL_FORMAL_PROGRESS_NO_BLOCKER_MOVE":
        decision = "PROOF_DEBT_DISCHARGE_PARTIAL_NO_BLOCKER_MOVE"
        next_action = "DECIDE_NECESSARY_BUT_INSUFFICIENT_VS_REPRIORITIZE_CLUSTER"
    else:
        decision = "PROOF_DEBT_DISCHARGE_FAILED"
        next_action = "REPRIORITIZE_CLUSTER_OR_FIX_MISSING_GATE_AND_RERUN_ONCE"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "tranche_report_present": tranche_report_path.exists(),
            "tranche_state_materialized": tranche_state != "",
            "bounded_decision_materialized": True,
        },
        "summary": {
            "decision": decision,
            "tranche_state": tranche_state,
            "blocker_facing_movement_observed": bool(summary.get("blocker_facing_movement_observed", False)),
            "formal_gap_closed_tied_to_blocker": bool(summary.get("formal_gap_closed_tied_to_blocker", False)),
            "route_falsification_of_blocker_removal_path": bool(summary.get("route_falsification_of_blocker_removal_path", False)),
            "next_action": next_action,
        },
        "source_bundle": {
            "tranche_report": _ptr(tranche_report_path),
        },
        "non_claim_boundary": "Repository-local proof-debt-first discharge decision artifact; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate proof-debt-first discharge decision report.")
    parser.add_argument("--tranche-report", type=Path, default=DEFAULT_TRANCHE_REPORT_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "proof_debt_first_formal_campaign_discharge_decision_20260411_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    tranche_report_path = ns.tranche_report if ns.tranche_report.is_absolute() else (REPO_ROOT / ns.tranche_report)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_report(tranche_report_path=tranche_report_path, captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "proof_debt_first_formal_campaign_discharge_decision_report: "
        f"decision={payload['summary']['decision']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
