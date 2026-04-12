from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import program_state_conversion_review_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _seed(
    tmp_path: Path,
    *,
    registration_outcome: str = "REVISED_SIGNAL_REGISTERED_AS_DIAGNOSTIC_ONLY",
    q1_answer: str = "DEEPER_BLOCKER_DEFINITION_REVIEW_REQUIRED",
    q2_answer: str = "THEORY_POSTURE_REVIEW_NOT_YET_REQUIRED",
    q3_answer: str = "PAUSE_REFRAME_NOT_YET_REQUIRED",
) -> tuple[Path, object]:
    reports_dir = tmp_path / "formal" / "output" / "reports"
    reports_dir.mkdir(parents=True, exist_ok=True)

    registration_path = reports_dir / "revised_signal_diagnostic_registration_20260411_v0.json"
    _write_json(
        registration_path,
        {
            "summary": {
                "registration_outcome": registration_outcome,
                "signal_id": "SEAM_INTEGRATION_COVERAGE_DELTA_GT_0",
                "signal_disposition": "DIAGNOSTIC_ONLY",
                "promotion_to_authoritative_blocked": True,
                "authoritative_signal_unchanged": "BLOCKER_TOKEN_CHANGE_REMAINS_AUTHORITATIVE",
                "no_loop_rule": "ONE_DIAGNOSTIC_SIGNAL_REGISTRATION_ONLY",
                "no_further_pilot_loops_honored": True,
                "next_action": "EXECUTE_PROGRAM_STATE_CONVERSION_REVIEW",
            }
        },
    )

    declaration_path = (
        tmp_path / "formal" / "docs" / "release"
        / "PROGRAM_STATE_CONVERSION_REVIEW_20260411_v0.json"
    )
    declaration_path.parent.mkdir(parents=True, exist_ok=True)
    _write_json(
        declaration_path,
        {
            "schema_id": "PROGRAM_STATE_CONVERSION_REVIEW_20260411_v0",
            "required_inputs": {
                "revised_signal_diagnostic_registration_report": "formal/output/reports/revised_signal_diagnostic_registration_20260411_v0.json",
            },
            "exhausted_explanations": [
                {"explanation_class": "LOCAL_PACKET_SELECTION", "status": "EXHAUSTED_UNDER_CURRENT_FILTER"},
                {"explanation_class": "ARCHITECTURE_AND_UNIT_SELECTION", "status": "EXHAUSTED_UNDER_CURRENT_FILTER"},
                {"explanation_class": "MOVEMENT_SIGNAL_BLINDNESS", "status": "INFORMATIVE_BUT_NOT_PROMOTION_BEARING"},
            ],
            "review_questions": [
                {"question_id": "Q1", "question": "Does the repo require a deeper blocker-definition review?", "default_answer": q1_answer, "rationale": "Three tiers exhausted."},
                {"question_id": "Q2", "question": "Does the repo require a theory-posture review?", "default_answer": q2_answer, "rationale": "Escalation path."},
                {"question_id": "Q3", "question": "Does the repo require a pause and reframe on what counts as executable scientific leverage?", "default_answer": q3_answer, "rationale": "Widest move."},
            ],
            "review_policy": {
                "eligible_outcomes": [
                    "DEEPER_BLOCKER_DEFINITION_REVIEW_REQUIRED",
                    "THEORY_POSTURE_REVIEW_REQUIRED",
                    "PAUSE_REFRAME_ON_EXECUTABLE_LEVERAGE_REQUIRED",
                ],
                "default_outcome": "DEEPER_BLOCKER_DEFINITION_REVIEW_REQUIRED",
                "default_next_action": "EXECUTE_DEEPER_BLOCKER_DEFINITION_REVIEW",
                "no_loop_rule": "ONE_PROGRAM_STATE_CONVERSION_REVIEW_ONLY",
                "no_further_pilot_loops_honored": True,
            },
        },
    )

    original = tool.REPO_ROOT
    tool.REPO_ROOT = tmp_path
    return declaration_path, original


def _run(tmp_path: Path, **seed_kwargs) -> dict:
    declaration_path, original = _seed(tmp_path, **seed_kwargs)
    try:
        return tool.build_report(
            declaration_path=declaration_path,
            captured_at_utc="2026-04-11T00:00:00Z",
        )
    finally:
        tool.REPO_ROOT = original


def test_default_deeper_blocker_definition_path(tmp_path: Path) -> None:
    """Default path: Q1=DEEPER_BLOCKER, Q2/Q3 not yet required → DEEPER_BLOCKER_DEFINITION_REVIEW_REQUIRED."""
    report = _run(tmp_path)
    summary = report["summary"]

    assert summary["review_outcome"] == "DEEPER_BLOCKER_DEFINITION_REVIEW_REQUIRED"
    assert summary["q1"] == "DEEPER_BLOCKER_DEFINITION_REVIEW_REQUIRED"
    assert summary["q2"] == "THEORY_POSTURE_REVIEW_NOT_YET_REQUIRED"
    assert summary["q3"] == "PAUSE_REFRAME_NOT_YET_REQUIRED"
    assert summary["next_action"] == "EXECUTE_DEEPER_BLOCKER_DEFINITION_REVIEW"
    assert summary["no_loop_rule"] == "ONE_PROGRAM_STATE_CONVERSION_REVIEW_ONLY"
    assert summary["no_further_pilot_loops_honored"] is True


def test_theory_posture_escalation_path(tmp_path: Path) -> None:
    """When Q2 fires theory-posture, outcome must escalate to THEORY_POSTURE_REVIEW_REQUIRED."""
    report = _run(
        tmp_path,
        q1_answer="DEEPER_BLOCKER_DEFINITION_REVIEW_REQUIRED",
        q2_answer="THEORY_POSTURE_REVIEW_REQUIRED",
        q3_answer="PAUSE_REFRAME_NOT_YET_REQUIRED",
    )
    summary = report["summary"]

    assert summary["review_outcome"] == "THEORY_POSTURE_REVIEW_REQUIRED"
    assert summary["next_action"] == "EXECUTE_THEORY_POSTURE_REVIEW"
    assert summary["no_loop_rule"] == "ONE_PROGRAM_STATE_CONVERSION_REVIEW_ONLY"
