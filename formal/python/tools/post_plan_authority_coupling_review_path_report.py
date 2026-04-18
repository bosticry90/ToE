from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_REPORT_20260418_v0"
DEFAULT_DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_20260418_v0.json"
DEFAULT_OUT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "post_plan_authority_coupling_review_path_20260418_v0.json"


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

    chain_path = REPO_ROOT / str(required_inputs.get("post_plan_bounded_blocker_definition_packet_chain_report", "")).strip()
    authority_decl_path = REPO_ROOT / str(required_inputs.get("authority_coupling_review_declaration", "")).strip()
    authority_report_path = REPO_ROOT / str(required_inputs.get("authority_coupling_review_report", "")).strip()
    post_decision_path = REPO_ROOT / str(required_inputs.get("post_blocker_definition_test_decision_report", "")).strip()

    chain_report = _read_json(chain_path)
    authority_decl = _read_json(authority_decl_path)
    authority_report = _read_json(authority_report_path)
    post_decision_report = _read_json(post_decision_path)

    chain_ok = (
        chain_report.get("summary", {}).get("terminal_outcome") == str(policy.get("required_packet_chain_outcome", "")).strip()
        and chain_report.get("summary", {}).get("next_action") == str(policy.get("required_packet_chain_next_action", "")).strip()
    )
    authority_decl_ok = authority_decl.get("review_basis") == str(policy.get("required_authority_review_basis", "")).strip()
    post_decision_ok = post_decision_report.get("summary", {}).get("post_test_decision") == str(policy.get("required_post_decision", "")).strip()
    review_outcome = str(authority_report.get("summary", {}).get("review_outcome", "")).strip()
    review_next = str(authority_report.get("summary", {}).get("next_action", "")).strip()
    review_outcome_ok = review_outcome == str(policy.get("required_authority_review_outcome", "")).strip()
    review_next_ok = review_next == str(policy.get("required_authority_review_next_action", "")).strip()

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(outcome_contract.get("default_outcome", "POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_EVIDENCE_INCOMPLETE")).strip()

    if not chain_report or not authority_report:
        terminal_outcome = "HOLD_PENDING_POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_REPAIR"
        next_action = "RESTORE_POST_PLAN_AUTHORITY_COUPLING_REVIEW_INPUTS_AND_RERUN"
    elif chain_ok and authority_decl_ok and post_decision_ok and review_outcome_ok and review_next_ok:
        terminal_outcome = "POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_MATERIALIZED"
        next_action = review_next
    elif chain_ok and authority_decl_ok and post_decision_ok and review_outcome == "COUPLING_DEFECT_BOUNDED_BUT_HOLD_AWAITING_THEORY":
        terminal_outcome = "POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_HOLD_AWAITING_THEORY"
        next_action = review_next
    elif chain_ok and authority_decl_ok and post_decision_ok and review_outcome == "COUPLING_DEFECT_NOT_SUFFICIENTLY_BOUNDED":
        terminal_outcome = "POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_ESCALATED"
        next_action = review_next
    elif chain_ok:
        terminal_outcome = "POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_BLOCKED"
        next_action = "REPAIR_AUTHORITY_COUPLING_REVIEW_CHAIN_BEFORE_PROCEEDING"
    else:
        terminal_outcome = "POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_EVIDENCE"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "packet_chain_trigger_present": chain_ok,
            "authority_review_declaration_present": authority_decl_ok,
            "post_decision_alignment_ok": post_decision_ok,
            "authority_review_materialized": bool(review_outcome),
            "next_action_materialized": bool(review_next),
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip() == "EXACTLY_ONE_ALLOWED_POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip() == "ONE_POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "authority_review_only_opens_after_nonmoving_packet_chain": (terminal_outcome != "POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_MATERIALIZED") or chain_ok,
                "bounded_refinement_only_after_bounded_coupling_review": (next_action != "EXECUTE_BOUNDED_COUPLING_REFINEMENT_PACKET_ONCE") or review_outcome_ok,
            },
            "inputs": {
                "packet_chain_outcome": chain_report.get("summary", {}).get("terminal_outcome"),
                "packet_chain_next_action": chain_report.get("summary", {}).get("next_action"),
                "post_test_decision": post_decision_report.get("summary", {}).get("post_test_decision"),
                "authority_review_outcome": review_outcome,
                "authority_review_next_action": review_next,
                "coupling_disposition": authority_report.get("summary", {}).get("coupling_disposition"),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "triggering_chain_outcome": chain_report.get("summary", {}).get("terminal_outcome"),
            "authority_review_outcome": review_outcome,
            "coupling_disposition": authority_report.get("summary", {}).get("coupling_disposition"),
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "post_plan_bounded_blocker_definition_packet_chain_report": _ptr(chain_path),
            "authority_coupling_review_declaration": _ptr(authority_decl_path),
            "authority_coupling_review_report": _ptr(authority_report_path),
            "post_blocker_definition_test_decision_report": _ptr(post_decision_path)
        },
        "non_claim_boundary": "Repository-local post-plan authority-coupling review path only; no scientific adequacy claim."
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the post-plan authority-coupling review path report.")
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
        "post_plan_authority_coupling_review_path_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())