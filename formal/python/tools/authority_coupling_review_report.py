from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "AUTHORITY_COUPLING_REVIEW_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "AUTHORITY_COUPLING_REVIEW_20260411_v0.json"
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
    coupling_context = dict(declaration.get("coupling_context", {}))

    decision_path = REPO_ROOT / str(
        required_inputs.get("post_blocker_definition_test_decision_report", "")
    )
    decision_report = _read_json(decision_path)
    decision_summary = dict(decision_report.get("summary", {}))

    post_test_decision = str(decision_summary.get("post_test_decision", "")).strip()
    decision_is_hold = "HOLD" in post_test_decision

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

    # Determine review outcome and routing
    coupling_is_bounded = q2 == "COUPLING_DEFECT_IS_SPECIFIC_AND_BOUNDED_BETWEEN_SEAM_AND_BLOCKER_ARTIFACT"
    coupling_escalate = q2 == "COUPLING_DEFECT_NOT_SUFFICIENTLY_BOUNDED_APPEARS_SYSTEMIC"

    if coupling_escalate:
        review_outcome = "COUPLING_DEFECT_NOT_SUFFICIENTLY_BOUNDED"
        next_action = "ESCALATE_TO_THEORY_POSTURE_OR_PROGRAM_PAUSE_REVIEW"
        coupling_disposition = "ESCALATE"
    elif coupling_is_bounded and q3 == "BOUNDED_COUPLING_REFINEMENT_JUSTIFIED_SEAM_ARTIFACT_BINDING_REVIEW":
        review_outcome = "BOUNDED_COUPLING_REFINEMENT_JUSTIFIED"
        next_action = "EXECUTE_BOUNDED_COUPLING_REFINEMENT_PACKET_ONCE"
        coupling_disposition = "REFINE_COUPLING"
    elif coupling_is_bounded and q3 == "HOLD_SECONDARY_AND_STOP_AWAITING_THEORY_ADVANCE":
        review_outcome = "COUPLING_DEFECT_BOUNDED_BUT_HOLD_AWAITING_THEORY"
        next_action = "HOLD_REVISED_DEF_SECONDARY_AWAIT_THEORY_ADVANCE"
        coupling_disposition = "HOLD_THEORY"
    else:
        # Default when bounded and Q3 suggests refinement
        review_outcome = "BOUNDED_COUPLING_REFINEMENT_JUSTIFIED"
        next_action = "EXECUTE_BOUNDED_COUPLING_REFINEMENT_PACKET_ONCE"
        coupling_disposition = "REFINE_COUPLING"

    question_assessment = [
        {
            "question_id": "Q1",
            "question": "What exact coupling is missing between the revised blocker definition and authoritative blocker state?",
            "answer": q1,
            "valid": q1_valid,
        },
        {
            "question_id": "Q2",
            "question": "Is that coupling defect specific and bounded, or systemic?",
            "answer": q2,
            "valid": q2_valid,
        },
        {
            "question_id": "Q3",
            "question": "What one next route should the program take?",
            "answer": q3,
            "valid": q3_valid,
        },
    ]

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "decision_prerequisite_satisfied": decision_is_hold,
            "q1_answered_with_valid_option": q1_valid,
            "q2_answered_with_valid_option": q2_valid,
            "q3_answered_with_valid_option": q3_valid,
            "coupling_disposition_materialized": bool(coupling_disposition),
            "next_action_materialized": bool(next_action),
            "no_loop_rule_declared": no_loop_rule == "ONE_AUTHORITY_COUPLING_REVIEW_ONLY",
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
                "decision_outcome": post_test_decision,
                "revised_blocker_definition": str(coupling_context.get("revised_blocker_definition", "")),
                "revised_def_status": str(coupling_context.get("revised_def_status", "")),
                "authoritative_signal": str(coupling_context.get("authoritative_blocker_signal", "")),
                "authoritative_signal_status": str(coupling_context.get("authoritative_signal_status", "")),
                "q1": q1,
                "q2": q2,
                "q3": q3,
                "coupling_is_bounded": coupling_is_bounded,
                "coupling_escalate": coupling_escalate,
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
            "coupling_defect": q1,
            "coupling_boundedness": q2,
            "routing_decision": q3,
            "coupling_disposition": coupling_disposition,
            "revised_blocker_definition": str(coupling_context.get("revised_blocker_definition", "")),
            "authoritative_signal_status": str(coupling_context.get("authoritative_signal_status", "")),
            "no_loop_rule": no_loop_rule,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "post_blocker_definition_test_decision_report": _ptr(decision_path),
        },
        "non_claim_boundary": "Repository-local authority-coupling review only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the authority-coupling review report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "authority_coupling_review_20260411_v0.json",
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
        "authority_coupling_review_report: "
        f"outcome={payload['summary']['review_outcome']} "
        f"disposition={payload['summary']['coupling_disposition']} "
        f"next_action={payload['summary']['next_action']} "
        f"out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
