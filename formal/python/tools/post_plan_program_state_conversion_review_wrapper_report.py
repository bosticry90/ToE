from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PLAN_PROGRAM_STATE_CONVERSION_REVIEW_WRAPPER_REPORT_20260418_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_PROGRAM_STATE_CONVERSION_REVIEW_WRAPPER_20260418_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_plan_program_state_conversion_review_wrapper_20260418_v0.json"
)


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(_read_text(path))


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    policy = dict(declaration.get("execution_policy", {}))
    outcome_contract = dict(declaration.get("outcome_contract", {}))

    sr_path = REPO_ROOT / str(required_inputs.get("post_plan_sr_theorem_gap_completion_tranche_report", "")).strip()
    conversion_decl_path = REPO_ROOT / str(required_inputs.get("program_state_conversion_review_declaration", "")).strip()
    conversion_report_path = REPO_ROOT / str(required_inputs.get("program_state_conversion_review_report", "")).strip()
    successor_path = REPO_ROOT / str(
        required_inputs.get("post_plan_deeper_blocker_definition_review_successor_tranche_report", "")
    ).strip()

    sr_report = _read_json(sr_path)
    conversion_decl = _read_json(conversion_decl_path)
    conversion_report = _read_json(conversion_report_path)
    successor_report = _read_json(successor_path)

    sr_ok = (
        sr_report.get("summary", {}).get("terminal_outcome")
        == str(policy.get("required_sr_outcome", "")).strip()
        and sr_report.get("summary", {}).get("next_action")
        == str(policy.get("required_sr_next_action", "")).strip()
    )
    conversion_decl_ok = (
        conversion_decl.get("review_basis")
        == str(policy.get("required_conversion_review_basis", "")).strip()
        and conversion_decl.get("review_policy", {}).get("no_loop_rule") == "ONE_PROGRAM_STATE_CONVERSION_REVIEW_ONLY"
    )
    conversion_report_ok = (
        conversion_report.get("summary", {}).get("review_outcome")
        == str(policy.get("required_conversion_review_outcome", "")).strip()
        and conversion_report.get("summary", {}).get("next_action")
        == str(policy.get("required_conversion_review_next_action", "")).strip()
    )
    successor_ok = (
        successor_report.get("summary", {}).get("terminal_outcome")
        == str(policy.get("required_successor_outcome", "")).strip()
        and successor_report.get("summary", {}).get("next_action")
        == str(policy.get("required_successor_next_action", "")).strip()
    )

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get(
            "default_outcome",
            "POST_PLAN_PROGRAM_STATE_CONVERSION_REVIEW_WRAPPER_EVIDENCE_INCOMPLETE",
        )
    ).strip()

    if not sr_report or not conversion_report:
        terminal_outcome = "HOLD_PENDING_POST_PLAN_PROGRAM_STATE_CONVERSION_REVIEW_WRAPPER_REPAIR"
        next_action = "RESTORE_POST_PLAN_PROGRAM_STATE_CONVERSION_REVIEW_WRAPPER_INPUTS_AND_RERUN"
    elif all([sr_ok, conversion_decl_ok, conversion_report_ok, successor_ok]):
        terminal_outcome = "POST_PLAN_PROGRAM_STATE_CONVERSION_REVIEW_WRAPPER_MATERIALIZED"
        next_action = str(policy.get("required_wrapper_next_action", "")).strip()
    elif all([sr_ok, conversion_decl_ok, conversion_report_ok]) and not successor_ok:
        terminal_outcome = "POST_PLAN_PROGRAM_STATE_CONVERSION_REVIEW_WRAPPER_BLOCKED"
        next_action = "RESTORE_EXISTING_PROGRAM_STATE_CONVERSION_REVIEW_DOWNSTREAM_PATH_BEFORE_ANY_NEW_QUEUE_DECISION"
    else:
        terminal_outcome = "POST_PLAN_PROGRAM_STATE_CONVERSION_REVIEW_WRAPPER_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_POST_PLAN_PROGRAM_STATE_CONVERSION_REVIEW_WRAPPER_EVIDENCE"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "sr_nonmoving_trigger_present": sr_ok,
            "conversion_review_declaration_present": conversion_decl_ok,
            "conversion_review_report_present": conversion_report_ok,
            "existing_downstream_successor_path_present": successor_ok,
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_POST_PLAN_PROGRAM_STATE_CONVERSION_REVIEW_WRAPPER_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_POST_PLAN_PROGRAM_STATE_CONVERSION_REVIEW_WRAPPER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "wrapper_only_opens_after_sr_nonmoving_trigger": (terminal_outcome != "POST_PLAN_PROGRAM_STATE_CONVERSION_REVIEW_WRAPPER_MATERIALIZED") or sr_ok,
                "queue_only_closes_after_existing_downstream_path_confirmed": (terminal_outcome != "POST_PLAN_PROGRAM_STATE_CONVERSION_REVIEW_WRAPPER_MATERIALIZED") or successor_ok,
            },
            "inputs": {
                "triggering_row": sr_report.get("summary", {}).get("target_row_id"),
                "sr_terminal_outcome": sr_report.get("summary", {}).get("terminal_outcome"),
                "sr_next_action": sr_report.get("summary", {}).get("next_action"),
                "conversion_review_basis": conversion_decl.get("review_basis"),
                "conversion_review_outcome": conversion_report.get("summary", {}).get("review_outcome"),
                "conversion_review_next_action": conversion_report.get("summary", {}).get("next_action"),
                "successor_outcome": successor_report.get("summary", {}).get("terminal_outcome"),
                "successor_next_action": successor_report.get("summary", {}).get("next_action"),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "triggering_row": sr_report.get("summary", {}).get("target_row_id"),
            "triggering_sr_outcome": sr_report.get("summary", {}).get("terminal_outcome"),
            "conversion_review_outcome": conversion_report.get("summary", {}).get("review_outcome"),
            "conversion_review_next_action": conversion_report.get("summary", {}).get("next_action"),
            "downstream_successor_outcome": successor_report.get("summary", {}).get("terminal_outcome"),
            "downstream_successor_next_action": successor_report.get("summary", {}).get("next_action"),
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "post_plan_sr_theorem_gap_completion_tranche_report": _ptr(sr_path),
            "program_state_conversion_review_declaration": _ptr(conversion_decl_path),
            "program_state_conversion_review_report": _ptr(conversion_report_path),
            "post_plan_deeper_blocker_definition_review_successor_tranche_report": _ptr(successor_path),
        },
        "non_claim_boundary": "Repository-local post-plan program-state conversion review wrapper only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the post-plan program-state conversion review wrapper report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
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
        "post_plan_program_state_conversion_review_wrapper_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())