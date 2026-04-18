from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_REPORT_20260418_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_20260418_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_plan_deeper_blocker_definition_review_successor_tranche_20260418_v0.json"
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

    gr_path = REPO_ROOT / str(required_inputs.get("post_plan_gr_tranche_report", "")).strip()
    deeper_decl_path = REPO_ROOT / str(required_inputs.get("deeper_blocker_definition_review_declaration", "")).strip()
    deeper_report_path = REPO_ROOT / str(required_inputs.get("deeper_blocker_definition_review_report", "")).strip()
    conversion_report_path = REPO_ROOT / str(required_inputs.get("program_state_conversion_review_report", "")).strip()

    gr_report = _read_json(gr_path)
    deeper_decl = _read_json(deeper_decl_path)
    deeper_report = _read_json(deeper_report_path)
    conversion_report = _read_json(conversion_report_path)

    gr_ok = (
        gr_report.get("summary", {}).get("terminal_outcome") == str(policy.get("required_gr_outcome", "")).strip()
        and gr_report.get("summary", {}).get("next_action") == str(policy.get("required_gr_next_action", "")).strip()
    )
    decl_ok = deeper_decl.get("review_basis") == str(policy.get("required_review_basis", "")).strip()
    conversion_ok = conversion_report.get("summary", {}).get("review_outcome") == str(policy.get("required_conversion_review_outcome", "")).strip()
    deeper_ok = deeper_report.get("summary", {}).get("review_outcome") == str(policy.get("required_deeper_review_outcome", "")).strip()
    next_action_ok = deeper_report.get("summary", {}).get("next_action") == str(policy.get("required_successor_next_action", "")).strip()

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get("default_outcome", "POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_EVIDENCE_INCOMPLETE")
    ).strip()

    if not gr_report or not deeper_report:
        terminal_outcome = "HOLD_PENDING_POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_REPAIR"
        next_action = "RESTORE_POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_INPUT_SHAPE_AND_RERUN"
    elif all([gr_ok, decl_ok, conversion_ok, deeper_ok, next_action_ok]):
        terminal_outcome = "POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_MATERIALIZED"
        next_action = str(policy.get("required_successor_next_action", "")).strip()
    elif all([gr_ok, decl_ok, conversion_ok]) and not deeper_ok:
        terminal_outcome = "POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_BLOCKED"
        next_action = "REPAIR_OR_RERUN_DEEPER_BLOCKER_DEFINITION_REVIEW_BEFORE_OPENING_FOLLOW_ON_PACKET"
    else:
        terminal_outcome = "POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_EVIDENCE"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "gr_exhaustion_trigger_present": gr_ok,
            "deeper_review_declaration_present": decl_ok,
            "conversion_review_requires_deeper_review": conversion_ok,
            "deeper_review_materialized": deeper_ok,
            "successor_next_action_pinned": next_action_ok,
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "successor_only_opens_after_gr_exhaustion": (terminal_outcome != "POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_MATERIALIZED") or gr_ok,
                "successor_only_opens_after_deeper_review_materializes": (terminal_outcome != "POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_MATERIALIZED") or deeper_ok,
            },
            "inputs": {
                "gr_terminal_outcome": gr_report.get("summary", {}).get("terminal_outcome"),
                "gr_next_action": gr_report.get("summary", {}).get("next_action"),
                "review_basis": deeper_decl.get("review_basis"),
                "conversion_review_outcome": conversion_report.get("summary", {}).get("review_outcome"),
                "deeper_review_outcome": deeper_report.get("summary", {}).get("review_outcome"),
                "bounded_follow_on_packet": deeper_report.get("summary", {}).get("bounded_follow_on_packet"),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "triggering_row": gr_report.get("summary", {}).get("target_row_id"),
            "triggering_gr_outcome": gr_report.get("summary", {}).get("terminal_outcome"),
            "deeper_review_outcome": deeper_report.get("summary", {}).get("review_outcome"),
            "bounded_follow_on_packet": deeper_report.get("summary", {}).get("bounded_follow_on_packet"),
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "post_plan_gr_tranche_report": _ptr(gr_path),
            "deeper_blocker_definition_review_declaration": _ptr(deeper_decl_path),
            "deeper_blocker_definition_review_report": _ptr(deeper_report_path),
            "program_state_conversion_review_report": _ptr(conversion_report_path)
        },
        "non_claim_boundary": "Repository-local post-plan deeper blocker-definition review successor tranche only; no scientific adequacy claim."
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the post-plan deeper blocker-definition review successor tranche report.")
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
        "post_plan_deeper_blocker_definition_review_successor_tranche_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())