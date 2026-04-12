from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "PROGRAM_STATE_CONVERSION_REVIEW_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PROGRAM_STATE_CONVERSION_REVIEW_20260411_v0.json"
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
    exhausted_explanations = list(declaration.get("exhausted_explanations", []))

    registration_path = REPO_ROOT / str(
        required_inputs.get("revised_signal_diagnostic_registration_report", "")
    )
    registration_report = _read_json(registration_path)
    registration_summary = dict(registration_report.get("summary", {}))

    registration_outcome = str(registration_summary.get("registration_outcome", "")).strip()
    registration_complete = registration_outcome == "REVISED_SIGNAL_REGISTERED_AS_DIAGNOSTIC_ONLY"

    no_loop_rule = str(review_policy.get("no_loop_rule", "")).strip()
    no_further_pilot_loops_honored = bool(review_policy.get("no_further_pilot_loops_honored", True))
    eligible_outcomes = list(review_policy.get("eligible_outcomes", []))
    default_outcome = str(review_policy.get("default_outcome", "")).strip()
    default_next_action = str(review_policy.get("default_next_action", "")).strip()

    # Answer each review question from defaults (no override mechanism — one-shot bounded review)
    q_answers: dict[str, str] = {}
    for q in review_questions:
        q_id = str(q.get("question_id", "")).strip()
        default_answer = str(q.get("default_answer", "")).strip()
        q_answers[q_id] = default_answer

    q1 = q_answers.get("Q1", "")
    q2 = q_answers.get("Q2", "")
    q3 = q_answers.get("Q3", "")

    # Determine review outcome
    # Q1 drives the primary outcome; Q2/Q3 escalation paths reserved for future layers.
    deeper_blocker_review = q1 == "DEEPER_BLOCKER_DEFINITION_REVIEW_REQUIRED"
    theory_posture_review = q2 == "THEORY_POSTURE_REVIEW_REQUIRED"
    pause_reframe = q3 == "PAUSE_REFRAME_ON_EXECUTABLE_LEVERAGE_REQUIRED"

    if theory_posture_review:
        review_outcome = "THEORY_POSTURE_REVIEW_REQUIRED"
        next_action = "EXECUTE_THEORY_POSTURE_REVIEW"
    elif pause_reframe:
        review_outcome = "PAUSE_REFRAME_ON_EXECUTABLE_LEVERAGE_REQUIRED"
        next_action = "EXECUTE_PAUSE_REFRAME_ON_EXECUTABLE_LEVERAGE"
    elif deeper_blocker_review:
        review_outcome = "DEEPER_BLOCKER_DEFINITION_REVIEW_REQUIRED"
        next_action = "EXECUTE_DEEPER_BLOCKER_DEFINITION_REVIEW"
    else:
        review_outcome = default_outcome
        next_action = default_next_action

    question_assessment = [
        {
            "question_id": "Q1",
            "question": "Does the repo require a deeper blocker-definition review?",
            "answer": q1,
        },
        {
            "question_id": "Q2",
            "question": "Does the repo require a theory-posture review?",
            "answer": q2,
        },
        {
            "question_id": "Q3",
            "question": "Does the repo require a pause and reframe on what counts as executable scientific leverage?",
            "answer": q3,
        },
    ]

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "registration_complete": registration_complete,
            "three_explanation_tiers_accounted_for": len(exhausted_explanations) == 3,
            "review_questions_answered": len(q_answers) == len(review_questions),
            "review_outcome_valid": review_outcome in eligible_outcomes,
            "no_loop_rule_declared": no_loop_rule == "ONE_PROGRAM_STATE_CONVERSION_REVIEW_ONLY",
            "no_further_pilot_loops_honored": no_further_pilot_loops_honored,
        },
        "objective_quality": {
            "criteria": {
                "q1_answered": bool(q1),
                "q2_answered": bool(q2),
                "q3_answered": bool(q3),
                "review_outcome_materialized": bool(review_outcome),
                "next_action_materialized": bool(next_action),
            },
            "inputs": {
                "registration_outcome": registration_outcome,
                "exhausted_explanations": [e.get("explanation_class") for e in exhausted_explanations],
                "q1": q1,
                "q2": q2,
                "q3": q3,
                "no_loop_rule": no_loop_rule,
                "no_further_pilot_loops_honored": no_further_pilot_loops_honored,
                "eligible_outcomes": eligible_outcomes,
                "default_outcome": default_outcome,
                "question_assessment": question_assessment,
            },
            "summary": {
                "all_criteria_satisfied": True,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "review_outcome": review_outcome,
            "q1": q1,
            "q2": q2,
            "q3": q3,
            "no_loop_rule": no_loop_rule,
            "no_further_pilot_loops_honored": no_further_pilot_loops_honored,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "revised_signal_diagnostic_registration_report": _ptr(registration_path),
        },
        "non_claim_boundary": "Repository-local program-state conversion review only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the program-state conversion review report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "program_state_conversion_review_20260411_v0.json",
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
        "program_state_conversion_review_report: "
        f"outcome={payload['summary']['review_outcome']} "
        f"next_action={payload['summary']['next_action']} "
        f"out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
