from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_ROBUSTNESS_GAP_REVIEW_RULING_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_ROBUSTNESS_GAP_REVIEW_RULING_20260412_v0.json"
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


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    contract = dict(declaration.get("ruling_contract", {}))

    execution_path = REPO_ROOT / str(
        required_inputs.get("bridge_robustness_gap_review_execution_report", "")
    ).strip()
    execution = _read_json(execution_path)
    execution_summary = dict(execution.get("summary", {}))

    execution_outcome = str(execution_summary.get("terminal_outcome", "")).strip()
    allowed_outcomes = [str(v) for v in contract.get("allowed_outcomes", [])]
    default_outcome = str(contract.get("default_outcome", "COMPARATOR_BOUND_HOLD_RETAINED")).strip()

    if execution_outcome in allowed_outcomes:
        terminal_outcome = execution_outcome
        ruling_status = "TERMINAL_OUTCOME_CONFIRMED"
    else:
        terminal_outcome = default_outcome
        ruling_status = "TERMINAL_OUTCOME_BLOCKED"

    if terminal_outcome == "ONE_BOUNDED_ROBUSTNESS_REFINEMENT_JUSTIFIED":
        next_action = "AUTHORIZE_ONE_BOUNDED_REFINEMENT_EXECUTION_PACKET"
    elif terminal_outcome == "COMPARATOR_BOUND_HOLD_RETAINED":
        next_action = "RETAIN_HOLD_AND_MONITOR_ROBUSTNESS_BOUNDARY"
    elif terminal_outcome == "PROBE_READINESS_CRITERIA_REQUIRE_REVISION":
        next_action = "REVISE_PROBE_READINESS_CRITERIA_ONCE"
    else:
        next_action = "RETIRE_PATH_AND_RECORD_FALSIFICATION"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "execution_terminal_outcome_present": bool(execution_outcome),
            "execution_terminal_outcome_allowed": execution_outcome in allowed_outcomes,
            "single_terminal_outcome_rule_declared": str(contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_ROBUSTNESS_GAP_RULING_OUTCOME",
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_BRIDGE_ROBUSTNESS_GAP_RULING_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in set(allowed_outcomes),
                "single_outcome_materialized": True,
                "ruling_status_materialized": bool(ruling_status),
            },
            "inputs": {
                "execution_terminal_outcome": execution_outcome,
                "allowed_outcomes": allowed_outcomes,
                "default_outcome": default_outcome,
            },
            "summary": {
                "all_criteria_satisfied": ruling_status == "TERMINAL_OUTCOME_CONFIRMED",
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "ruling_status": ruling_status,
            "terminal_outcome": terminal_outcome,
            "single_terminal_outcome_enforced": True,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_robustness_gap_review_execution_report": _ptr(execution_path),
        },
        "non_claim_boundary": "Repository-local bridge robustness-gap review ruling report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 bridge robustness-gap review ruling report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_robustness_gap_review_ruling_20260412_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    declaration_path = ns.declaration if ns.declaration.is_absolute() else (REPO_ROOT / ns.declaration)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_report(declaration_path=declaration_path, captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "qm_stat_rl10_discrete_transition_bridge_robustness_gap_review_ruling_report: "
        f"ruling_status={payload['summary']['ruling_status']} "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())