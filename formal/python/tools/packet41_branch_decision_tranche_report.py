from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "PACKET41_BRANCH_DECISION_TRANCHE_20260411_v0"

DEFAULT_HOLD_FORK_COMPONENT_LIFT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "packet41_component_lift_tranche_20260411_v0.json"
)
DEFAULT_RETROSPECTIVE_COMPONENT_LIFT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "packet41_component_lift_retrospective_tranche_20260411_v0.json"
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
    try:
        return str(path.relative_to(REPO_ROOT)).replace("\\", "/")
    except ValueError:
        return str(path).replace("\\", "/")


def build_report(
    hold_fork_component_lift_path: Path,
    retrospective_component_lift_path: Path,
    captured_at_utc: str | None,
) -> dict[str, Any]:
    hold_fork = _read_json(hold_fork_component_lift_path)
    retrospective = _read_json(retrospective_component_lift_path)

    stop_rule = hold_fork.get("summary", {}).get("stop_rule", {})
    stop_rule_triggered = bool(stop_rule.get("triggered", False))

    retrospective_lift_observed = bool(retrospective.get("summary", {}).get("component_lift_observed", False))
    retrospective_outcome = str(retrospective.get("summary", {}).get("outcome", "NO_LIFT"))

    if stop_rule_triggered and (not retrospective_lift_observed):
        decision = "DEFER_OR_RECLASSIFY_PACKET41_NEAR_TERM_BLOCKER_BURN_LANE"
        decision_reason = (
            "hold-fork no-lift stop-rule triggered and retrospective component lift remained false"
        )
        next_action = "ROUTE_TO_REWORK_LEDGER_WITH_DEFERRED_PACKET41_BURN"
    elif stop_rule_triggered and retrospective_lift_observed:
        decision = "CONTINUE_PACKET41_CLEARANCE_WITH_UPDATED_REVIEW_LAYER_STATE"
        decision_reason = "hold-fork stop-rule triggered but retrospective component lift succeeded"
        next_action = "RERUN_PACKET41_SUCCESSOR_DECISION_ENFORCEMENT"
    else:
        decision = "NO_BRANCH_DECISION_REQUIRED"
        decision_reason = "stop-rule not triggered"
        next_action = "CONTINUE_CURRENT_PACKET41_TRANCHE_PLAN"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "target": "PACKET41_STOP_RULE_BRANCH_DECISION",
        "criteria": {
            "hold_fork_stop_rule_triggered": stop_rule_triggered,
            "retrospective_component_lift_observed": retrospective_lift_observed,
        },
        "summary": {
            "decision": decision,
            "decision_reason": decision_reason,
            "next_action": next_action,
            "retrospective_outcome": retrospective_outcome,
        },
        "source_bundle": {
            "hold_fork_component_lift_report": _ptr(hold_fork_component_lift_path),
            "retrospective_component_lift_report": _ptr(retrospective_component_lift_path),
        },
        "non_claim_boundary": "Repository-local Packet41 branch decision tranche artifact; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate Packet41 stop-rule branch decision tranche report.")
    parser.add_argument(
        "--hold-fork-component-lift-path",
        type=Path,
        default=DEFAULT_HOLD_FORK_COMPONENT_LIFT_PATH,
    )
    parser.add_argument(
        "--retrospective-component-lift-path",
        type=Path,
        default=DEFAULT_RETROSPECTIVE_COMPONENT_LIFT_PATH,
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "packet41_branch_decision_tranche_20260411_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    hold_fork_path = (
        ns.hold_fork_component_lift_path
        if ns.hold_fork_component_lift_path.is_absolute()
        else (REPO_ROOT / ns.hold_fork_component_lift_path)
    )
    retrospective_path = (
        ns.retrospective_component_lift_path
        if ns.retrospective_component_lift_path.is_absolute()
        else (REPO_ROOT / ns.retrospective_component_lift_path)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_report(
        hold_fork_component_lift_path=hold_fork_path,
        retrospective_component_lift_path=retrospective_path,
        captured_at_utc=ns.captured_at_utc,
    )

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"packet41_branch_decision_tranche_report: decision={payload['summary']['decision']} out={out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
