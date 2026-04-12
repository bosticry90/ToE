from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import deeper_blocker_definition_review_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _seed(
    tmp_path: Path,
    *,
    conversion_review_outcome: str = "DEEPER_BLOCKER_DEFINITION_REVIEW_REQUIRED",
    q1_answer: str = "BLOCKER_TOKEN_CHANGE_DEFINITION_TOO_STRICT_OR_MONITORING_WRONG_ARTIFACT",
    q2_answer: str = "REVISED_BLOCKER_DEF_SEAM_ROW_STATE_TRANSITION_WITH_TRANSPORT_COHERENCE_CHECK",
    q3_answer: str = "ONE_SEAM_ROW_BLOCKER_DEFINITION_TEST_UNDER_REVISED_CRITERIA",
) -> tuple[Path, object]:
    """Return (declaration_path, original_repo_root)."""
    reports_dir = tmp_path / "formal" / "output" / "reports"
    reports_dir.mkdir(parents=True, exist_ok=True)

    conversion_review_path = reports_dir / "program_state_conversion_review_20260411_v0.json"
    _write_json(
        conversion_review_path,
        {
            "summary": {
                "review_outcome": conversion_review_outcome,
                "q1": "DEEPER_BLOCKER_DEFINITION_REVIEW_REQUIRED",
                "q2": "THEORY_POSTURE_REVIEW_NOT_YET_REQUIRED",
                "q3": "PAUSE_REFRAME_NOT_YET_REQUIRED",
                "no_loop_rule": "ONE_PROGRAM_STATE_CONVERSION_REVIEW_ONLY",
                "no_further_pilot_loops_honored": True,
                "next_action": "EXECUTE_DEEPER_BLOCKER_DEFINITION_REVIEW",
            }
        },
    )

    declaration_path = (
        tmp_path / "formal" / "docs" / "release"
        / "DEEPER_BLOCKER_DEFINITION_REVIEW_20260411_v0.json"
    )
    declaration_path.parent.mkdir(parents=True, exist_ok=True)

    _write_json(
        declaration_path,
        {
            "schema_id": "DEEPER_BLOCKER_DEFINITION_REVIEW_20260411_v0",
            "required_inputs": {
                "program_state_conversion_review_report": "formal/output/reports/program_state_conversion_review_20260411_v0.json",
            },
            "current_blocker_regime": {
                "authoritative_signal": "BLOCKER_TOKEN_CHANGE_REMAINS_AUTHORITATIVE",
                "signal_status": "NEVER_FIRED_IN_ANY_EXECUTION",
                "blocker_definition_implicit": "LEDGER_STATE_CHANGE_ATTRIBUTABLE_TO_SINGLE_BLOCKER_TOKEN_FLUX",
                "defect_assessment": "CURRENT_DEFINITION_TOO_STRICT_OR_WRONG_ARTIFACT_MONITORED",
            },
            "diagnostic_signal_available": {
                "diagnostic_signal": "SEAM_INTEGRATION_COVERAGE_DELTA_GT_0",
                "signal_status": "FIRED_IN_BOUNDED_PILOT",
                "blocker_definition_implicit": "TRANSPORT_WITNESS_BOUND_AND_BRIDGE_OBJECT_MATERIALIZED_FOR_SEAM_ROW",
            },
            "review_questions": [
                {"question_id": "Q1", "question": "What exact blocker definition is currently failing?", "default_answer": q1_answer},
                {"question_id": "Q2", "question": "Which measurable event should count as blocker movement (middle ground)?", "default_answer": q2_answer},
                {"question_id": "Q3", "question": "What one bounded follow-on packet would test the revised definition?", "default_answer": q3_answer},
            ],
            "review_policy": {
                "eligible_q1_answers": [
                    "BLOCKER_TOKEN_CHANGE_DEFINITION_TOO_STRICT_OR_MONITORING_WRONG_ARTIFACT",
                    "BLOCKER_TOKEN_CHANGE_DEFINITION_WRONG",
                    "BLOCKER_MONITORING_TARGETING_WRONG_ARTIFACT",
                ],
                "eligible_q2_answers": [
                    "REVISED_BLOCKER_DEF_SEAM_ROW_STATE_TRANSITION_WITH_TRANSPORT_COHERENCE_CHECK",
                    "REVISED_BLOCKER_DEF_BRIDGING_EVENT_WITH_LEDGER_CORRELATION",
                    "REVISED_BLOCKER_DEF_QM_STAT_UNIFIED_THEOREM_SURFACE_DELTA",
                ],
                "eligible_q3_answers": [
                    "ONE_SEAM_ROW_BLOCKER_DEFINITION_TEST_UNDER_REVISED_CRITERIA",
                    "SUBSYSTEM_BLOCKER_DEFINITION_TEST_BOUNDED_ONCE",
                    "BOUNDED_MULTIPLE_ROW_BLOCKER_DEFINITION_COMPARISON_TEST",
                ],
                "default_q1_answer": q1_answer,
                "default_q2_answer": q2_answer,
                "default_q3_answer": q3_answer,
                "no_loop_rule": "ONE_DEEPER_BLOCKER_DEFINITION_REVIEW_ONLY",
                "bounded_follow_on_once_only_policy": True,
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


def test_default_blocker_definition_review_path(tmp_path: Path) -> None:
    """Default path: Q1=strict-definition, Q2=seam-coherence, Q3=one-seam-test → MATERIALIZED."""
    report = _run(tmp_path)
    summary = report["summary"]

    assert summary["review_outcome"] == "DEEPER_BLOCKER_DEFINITION_REVIEW_MATERIALIZED"
    assert summary["q1"] == "BLOCKER_TOKEN_CHANGE_DEFINITION_TOO_STRICT_OR_MONITORING_WRONG_ARTIFACT"
    assert summary["q2"] == "REVISED_BLOCKER_DEF_SEAM_ROW_STATE_TRANSITION_WITH_TRANSPORT_COHERENCE_CHECK"
    assert summary["q3"] == "ONE_SEAM_ROW_BLOCKER_DEFINITION_TEST_UNDER_REVISED_CRITERIA"
    assert summary["current_authoritative_signal"] == "BLOCKER_TOKEN_CHANGE_REMAINS_AUTHORITATIVE"
    assert summary["authoritative_signal_status"] == "NEVER_FIRED_IN_ANY_EXECUTION"
    assert summary["revised_blocker_definition_candidate"] == "REVISED_BLOCKER_DEF_SEAM_ROW_STATE_TRANSITION_WITH_TRANSPORT_COHERENCE_CHECK"
    assert summary["bounded_follow_on_packet"] == "ONE_SEAM_ROW_BLOCKER_DEFINITION_TEST_UNDER_REVISED_CRITERIA"
    assert summary["no_loop_rule"] == "ONE_DEEPER_BLOCKER_DEFINITION_REVIEW_ONLY"
    assert summary["next_action"] == "EXECUTE_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_ONCE"


def test_review_blocked_when_prerequisite_missing(tmp_path: Path) -> None:
    """When conversion review outcome is not DEEPER_BLOCKER_DEFINITION_REVIEW_REQUIRED, review must be blocked."""
    report = _run(
        tmp_path,
        conversion_review_outcome="THEORY_POSTURE_REVIEW_REQUIRED",
    )
    summary = report["summary"]

    assert summary["review_outcome"] == "REVIEW_BLOCKED_MISSING_PREREQUISITE"
