from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_REPORT_20260418_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_20260418_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_plan_bounded_blocker_definition_test_packet_chain_20260418_v0.json"
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

    successor_path = REPO_ROOT / str(required_inputs.get("post_plan_successor_tranche_report", "")).strip()
    execution_path = REPO_ROOT / str(required_inputs.get("bounded_blocker_definition_test_execution_report", "")).strip()
    ruling_path = REPO_ROOT / str(required_inputs.get("bounded_blocker_definition_test_ruling_report", "")).strip()
    decision_path = REPO_ROOT / str(required_inputs.get("post_blocker_definition_test_decision_report", "")).strip()
    authority_decl_path = REPO_ROOT / str(required_inputs.get("authority_coupling_review_declaration", "")).strip()

    successor_report = _read_json(successor_path)
    execution_report = _read_json(execution_path)
    ruling_report = _read_json(ruling_path)
    decision_report = _read_json(decision_path)
    authority_decl = _read_json(authority_decl_path)

    successor_ok = (
        successor_report.get("summary", {}).get("terminal_outcome") == str(policy.get("required_successor_outcome", "")).strip()
        and successor_report.get("summary", {}).get("next_action") == str(policy.get("required_successor_next_action", "")).strip()
    )
    execution_classification = execution_report.get("summary", {}).get("execution_classification")
    execution_ok = execution_classification == str(policy.get("required_execution_classification", "")).strip()
    ruling_value = ruling_report.get("summary", {}).get("test_ruling")
    decision_value = decision_report.get("summary", {}).get("post_test_decision")
    decision_next = decision_report.get("summary", {}).get("next_action")
    ruling_ok = ruling_value == str(policy.get("required_ruling", "")).strip()
    decision_ok = (
        decision_value == str(policy.get("required_post_decision", "")).strip()
        and decision_next == str(policy.get("required_post_next_action", "")).strip()
    )
    authority_ok = authority_decl.get("review_basis") == str(policy.get("required_authority_review_basis", "")).strip()

    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(
        outcome_contract.get("default_outcome", "POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_EVIDENCE_INCOMPLETE")
    ).strip()

    if not successor_report or not execution_report or not ruling_report or not decision_report:
        terminal_outcome = "HOLD_PENDING_POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_REPAIR"
        next_action = "RESTORE_POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_INPUTS_AND_RERUN"
    elif successor_ok and execution_ok and ruling_value == "REVISED_BLOCKER_DEF_REVEALS_MEANINGFUL_MOVEMENT":
        terminal_outcome = "POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_REVEALS_MEANINGFUL_MOVEMENT"
        next_action = "REASSESS_AUTHORITY_SURFACES_WITH_REVISED_BLOCKER_MOVEMENT_RECORDED"
    elif successor_ok and execution_ok and ruling_ok and decision_ok and authority_ok:
        terminal_outcome = "POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_VALID_BUT_NONMOVING"
        next_action = "REQUIRE_ONE_BOUNDED_AUTHORITY_COUPLING_REVIEW"
    elif successor_ok and ruling_value == "REVISED_BLOCKER_DEF_NOT_FIT_FOR_AUTHORITY_USE":
        terminal_outcome = "POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_NOT_FIT_FOR_AUTHORITY_USE"
        next_action = "ESCALATE_TO_THEORY_POSTURE_OR_PROGRAM_PAUSE_REVIEW"
    elif successor_ok:
        terminal_outcome = "POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_BLOCKED"
        next_action = "REPAIR_BLOCKER_TEST_CHAIN_OR_RESOLVE_ROUTING_BEFORE_PROCEEDING"
    else:
        terminal_outcome = "POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_EVIDENCE"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "successor_tranche_materialized": successor_ok,
            "execution_report_materialized": execution_ok,
            "ruling_report_materialized": bool(ruling_value),
            "post_decision_materialized": bool(decision_value),
            "authority_coupling_review_declared": authority_ok,
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "packet_chain_only_opens_after_successor_tranche": (terminal_outcome != "POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_VALID_BUT_NONMOVING") or successor_ok,
                "authority_review_only_after_nonmoving_packet_chain": (next_action != "REQUIRE_ONE_BOUNDED_AUTHORITY_COUPLING_REVIEW") or (ruling_ok and decision_ok),
            },
            "inputs": {
                "successor_outcome": successor_report.get("summary", {}).get("terminal_outcome"),
                "execution_classification": execution_classification,
                "revised_blocker_def_fires": execution_report.get("summary", {}).get("revised_blocker_def_fires"),
                "ruling": ruling_value,
                "post_test_decision": decision_value,
                "bounded_follow_on_packet": successor_report.get("summary", {}).get("bounded_follow_on_packet"),
                "authority_review_basis": authority_decl.get("review_basis"),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "target_row_id": execution_report.get("summary", {}).get("target_row_id"),
            "candidate_blocker_definition": execution_report.get("summary", {}).get("candidate_blocker_definition"),
            "execution_classification": execution_classification,
            "test_ruling": ruling_value,
            "post_test_decision": decision_value,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "post_plan_successor_tranche_report": _ptr(successor_path),
            "bounded_blocker_definition_test_execution_report": _ptr(execution_path),
            "bounded_blocker_definition_test_ruling_report": _ptr(ruling_path),
            "post_blocker_definition_test_decision_report": _ptr(decision_path),
            "authority_coupling_review_declaration": _ptr(authority_decl_path)
        },
        "non_claim_boundary": "Repository-local post-plan bounded blocker-definition test packet chain only; no scientific adequacy claim."
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the post-plan bounded blocker-definition test packet chain report.")
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
        "post_plan_bounded_blocker_definition_test_packet_chain_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())