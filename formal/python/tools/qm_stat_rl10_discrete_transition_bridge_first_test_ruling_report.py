from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_FIRST_TEST_RULING_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_FIRST_TEST_RULING_20260412_v0.json"
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
    ruling_contract = dict(declaration.get("ruling_contract", {}))

    execution_path = REPO_ROOT / str(required_inputs.get("bridge_first_test_execution_report", "")).strip()
    execution = _read_json(execution_path)
    execution_summary = dict(execution.get("summary", {}))

    terminal_outcome = str(execution_summary.get("terminal_outcome", "")).strip()
    allowed_outcomes = [str(v) for v in ruling_contract.get("allowed_outcomes", [])]
    default_ruling = str(ruling_contract.get("default_ruling", "BRIDGE_SEAM_INTERNAL_ONLY")).strip()

    if terminal_outcome in allowed_outcomes:
        ruling = terminal_outcome
        ruling_status = "TERMINAL_OUTCOME_CONFIRMED"
    else:
        ruling = default_ruling
        ruling_status = "TERMINAL_OUTCOME_BLOCKED"

    if ruling == "BRIDGE_SEAM_SIGNAL_PRODUCED":
        next_action = "OPEN_NEXT_BOUNDED_SIGNAL_VALIDATION_TRANCHE"
    elif ruling == "BRIDGE_SEAM_INTERNAL_ONLY":
        next_action = "MAINTAIN_INTERNAL_ONLY_POSTURE"
    elif ruling == "BRIDGE_SEAM_PATH_FALSIFIED":
        next_action = "RETIRE_PATH_AND_LOG_FALSIFICATION"
    else:
        next_action = "DECLARE_MISSING_STRUCTURE_BEFORE_NEXT_TRANCHE"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "execution_terminal_outcome_present": bool(terminal_outcome),
            "execution_terminal_outcome_allowed": terminal_outcome in allowed_outcomes,
            "single_terminal_outcome_rule_declared": str(ruling_contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_TERMINAL_OUTCOME",
            "no_loop_rule_declared": str(ruling_contract.get("no_loop_rule", "")).strip()
            == "ONE_BRIDGE_SEAM_FIRST_TEST_RULING_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "single_terminal_outcome_materialized": True,
                "allowed_outcome_materialized": ruling in set(allowed_outcomes),
                "ruling_status_materialized": bool(ruling_status),
            },
            "inputs": {
                "execution_terminal_outcome": terminal_outcome,
                "allowed_outcomes": allowed_outcomes,
                "default_ruling": default_ruling,
            },
            "summary": {
                "all_criteria_satisfied": ruling_status == "TERMINAL_OUTCOME_CONFIRMED",
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "ruling_status": ruling_status,
            "terminal_outcome": ruling,
            "single_terminal_outcome_enforced": True,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_first_test_execution_report": _ptr(execution_path),
        },
        "non_claim_boundary": "Repository-local bridge seam first-test ruling report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 bridge seam first-test ruling report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_first_test_ruling_20260412_v0.json",
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
        "qm_stat_rl10_discrete_transition_bridge_first_test_ruling_report: "
        f"ruling_status={payload['summary']['ruling_status']} "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())