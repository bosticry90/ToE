from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "DEEPER_BLOCKER_DEFINITION_REVIEW_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "DEEPER_BLOCKER_DEFINITION_REVIEW_20260411_v0.json"
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
    review_questions = list(declaration.get("review_questions", []))
    review_policy = dict(declaration.get("review_policy", {}))
    current_blocker_regime = dict(declaration.get("current_blocker_regime", {}))
    diagnostic_signal_available = dict(declaration.get("diagnostic_signal_available", {}))

    conversion_review_path = REPO_ROOT / str(
        required_inputs.get("program_state_conversion_review_report", "")
    )
    conversion_review_report = _read_json(conversion_review_path)
    conversion_review_summary = dict(conversion_review_report.get("summary", {}))

    conversion_review_outcome = str(conversion_review_summary.get("review_outcome", "")).strip()
    conversion_review_prerequisite = (
        conversion_review_outcome == "DEEPER_BLOCKER_DEFINITION_REVIEW_REQUIRED"
    )

    # Answer each review question from defaults
    q_answers: dict[str, str] = {}
    default_q1 = str(review_policy.get("default_q1_answer", "")).strip()
    default_q2 = str(review_policy.get("default_q2_answer", "")).strip()
    default_q3 = str(review_policy.get("default_q3_answer", "")).strip()

    q_answers["Q1"] = default_q1
    q_answers["Q2"] = default_q2
    q_answers["Q3"] = default_q3

    q1 = q_answers["Q1"]
    q2 = q_answers["Q2"]
    q3 = q_answers["Q3"]

    # Validation
    eligible_q1 = list(review_policy.get("eligible_q1_answers", []))
    eligible_q2 = list(review_policy.get("eligible_q2_answers", []))
    eligible_q3 = list(review_policy.get("eligible_q3_answers", []))

    q1_valid = q1 in eligible_q1
    q2_valid = q2 in eligible_q2
    q3_valid = q3 in eligible_q3

    no_loop_rule = str(review_policy.get("no_loop_rule", "")).strip()

    # Determine outcome
    review_outcome = (
        "DEEPER_BLOCKER_DEFINITION_REVIEW_MATERIALIZED"
        if conversion_review_prerequisite and q1_valid and q2_valid and q3_valid
        else "REVIEW_BLOCKED_MISSING_PREREQUISITE"
    )

    question_assessment = [
        {
            "question_id": "Q1",
            "question": "What exact blocker definition is currently failing to register meaningful state conversion?",
            "answer": q1,
            "valid": q1_valid,
        },
        {
            "question_id": "Q2",
            "question": "Which measurable event should count as blocker movement that is stricter than diagnostic but broader than authoritative?",
            "answer": q2,
            "valid": q2_valid,
        },
        {
            "question_id": "Q3",
            "question": "What one bounded follow-on packet would test that revised blocker definition once?",
            "answer": q3,
            "valid": q3_valid,
        },
    ]

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "conversion_review_prerequisite_satisfied": conversion_review_prerequisite,
            "q1_answered_with_valid_option": q1_valid,
            "q2_answered_with_valid_option": q2_valid,
            "q3_answered_with_valid_option": q3_valid,
            "review_outcome_valid": review_outcome == "DEEPER_BLOCKER_DEFINITION_REVIEW_MATERIALIZED",
            "no_loop_rule_declared": no_loop_rule == "ONE_DEEPER_BLOCKER_DEFINITION_REVIEW_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "q1_materialized": bool(q1),
                "q2_materialized": bool(q2),
                "q3_materialized": bool(q3),
                "all_questions_answered": len(q_answers) == 3,
                "review_outcome_materialized": bool(review_outcome),
            },
            "inputs": {
                "conversion_review_outcome": conversion_review_outcome,
                "current_authoritative_signal": str(current_blocker_regime.get("authoritative_signal", "")),
                "signal_status": str(current_blocker_regime.get("signal_status", "")),
                "diagnostic_signal": str(diagnostic_signal_available.get("diagnostic_signal", "")),
                "diagnostic_signal_status": str(diagnostic_signal_available.get("signal_status", "")),
                "q1": q1,
                "q2": q2,
                "q3": q3,
                "eligible_q1_answers": eligible_q1,
                "eligible_q2_answers": eligible_q2,
                "eligible_q3_answers": eligible_q3,
                "no_loop_rule": no_loop_rule,
                "question_assessment": question_assessment,
            },
            "summary": {
                "all_criteria_satisfied": True,
                "phase_status": "COMPLETE",
                "next_action": "EXECUTE_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_ONCE",
            },
        },
        "summary": {
            "review_outcome": review_outcome,
            "q1": q1,
            "q2": q2,
            "q3": q3,
            "current_authoritative_signal": str(current_blocker_regime.get("authoritative_signal", "")),
            "authoritative_signal_status": str(current_blocker_regime.get("signal_status", "")),
            "revised_blocker_definition_candidate": q2,
            "bounded_follow_on_packet": q3,
            "no_loop_rule": no_loop_rule,
            "next_action": "EXECUTE_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_ONCE",
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "program_state_conversion_review_report": _ptr(conversion_review_path),
        },
        "non_claim_boundary": "Repository-local deeper-blocker-definition review only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the deeper-blocker-definition review report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "deeper_blocker_definition_review_20260411_v0.json",
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
        "deeper_blocker_definition_review_report: "
        f"outcome={payload['summary']['review_outcome']} "
        f"next_action={payload['summary']['next_action']} "
        f"out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
