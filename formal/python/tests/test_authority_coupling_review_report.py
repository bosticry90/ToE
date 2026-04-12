from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import authority_coupling_review_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _seed(
    tmp_path: Path,
    *,
    post_test_decision: str = "HOLD_REVISED_BLOCKER_DEF_AS_SECONDARY_REQUIRE_AUTHORITY_COUPLING_REVIEW",
    q1_answer: str = "REVISED_DEF_FIRES_WITHOUT_CORRESPONDING_BLOCKER_ARTIFACT_FLUX_IN_LEDGER",
    q2_answer: str = "COUPLING_DEFECT_IS_SPECIFIC_AND_BOUNDED_BETWEEN_SEAM_AND_BLOCKER_ARTIFACT",
    q3_answer: str = "BOUNDED_COUPLING_REFINEMENT_JUSTIFIED_SEAM_ARTIFACT_BINDING_REVIEW",
) -> tuple[Path, object]:
    """Return (declaration_path, original_repo_root)."""
    reports_dir = tmp_path / "formal" / "output" / "reports"
    reports_dir.mkdir(parents=True, exist_ok=True)

    decision_path = reports_dir / "post_blocker_definition_test_decision_20260411_v0.json"
    _write_json(
        decision_path,
        {
            "summary": {
                "post_test_decision": post_test_decision,
                "revised_signal_disposition": "HOLD_SECONDARY",
                "test_ruling": "REVISED_BLOCKER_DEF_VALID_BUT_NONMOVING",
                "revised_blocker_def_fires": True,
                "authoritative_fires": False,
                "no_loop_rule": "ONE_POST_BLOCKER_DEFINITION_TEST_DECISION_ONLY",
                "next_action": "REQUIRE_ONE_BOUNDED_AUTHORITY_COUPLING_REVIEW",
            }
        },
    )

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "AUTHORITY_COUPLING_REVIEW_20260411_v0.json"
    )
    declaration_path.parent.mkdir(parents=True, exist_ok=True)

    _write_json(
        declaration_path,
        {
            "schema_id": "AUTHORITY_COUPLING_REVIEW_20260411_v0",
            "required_inputs": {
                "post_blocker_definition_test_decision_report": "formal/output/reports/post_blocker_definition_test_decision_20260411_v0.json",
            },
            "coupling_context": {
                "revised_blocker_definition": "REVISED_BLOCKER_DEF_SEAM_ROW_STATE_TRANSITION_WITH_TRANSPORT_COHERENCE_CHECK",
                "revised_def_status": "VALID_FIRES_BUT_NONMOVING",
                "authoritative_blocker_signal": "BLOCKER_TOKEN_CHANGE_REMAINS_AUTHORITATIVE",
                "authoritative_signal_status": "NEVER_FIRES_IN_ANY_EXECUTION",
                "coupling_question": "Why does revised def fire without authoritative blocker movement?",
            },
            "review_questions": [
                {
                    "question_id": "Q1",
                    "question": "What exact coupling is missing between revised def and authoritative blocker?",
                    "default_answer": q1_answer,
                },
                {
                    "question_id": "Q2",
                    "question": "Is that coupling defect specific and bounded, or systemic?",
                    "default_answer": q2_answer,
                },
                {
                    "question_id": "Q3",
                    "question": "What one next route?",
                    "default_answer": q3_answer,
                },
            ],
            "review_policy": {
                "eligible_q1_answers": [
                    "REVISED_DEF_FIRES_WITHOUT_CORRESPONDING_BLOCKER_ARTIFACT_FLUX_IN_LEDGER",
                    "REVISED_DEF_MONITORS_SEAM_COHERENCE_BLOCKER_TOKEN_MONITORS_ARTIFACT_STATE",
                    "COUPLING_DEFECT_IS_ARTIFACT_MISMATCH_NOT_SIGNAL_WEAKNESS",
                ],
                "eligible_q2_answers": [
                    "COUPLING_DEFECT_IS_SPECIFIC_AND_BOUNDED_BETWEEN_SEAM_AND_BLOCKER_ARTIFACT",
                    "COUPLING_DEFECT_NOT_SUFFICIENTLY_BOUNDED_APPEARS_SYSTEMIC",
                    "COUPLING_DEFECT_UNCLEAR_REQUIRES_BROADER_INVESTIGATION",
                ],
                "eligible_q3_answers": [
                    "BOUNDED_COUPLING_REFINEMENT_JUSTIFIED_SEAM_ARTIFACT_BINDING_REVIEW",
                    "HOLD_SECONDARY_AND_STOP_AWAITING_THEORY_ADVANCE",
                    "ESCALATE_TO_THEORY_POSTURE_OR_PROGRAM_PAUSE_REVIEW",
                ],
                "default_q1_answer": q1_answer,
                "default_q2_answer": q2_answer,
                "default_q3_answer": q3_answer,
                "no_loop_rule": "ONE_AUTHORITY_COUPLING_REVIEW_ONLY",
                "bounded_next_action_once_only_policy": True,
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


def test_default_bounded_coupling_refinement_path(tmp_path: Path) -> None:
    """Default path: Q2=bounded, Q3=refinement → BOUNDED_COUPLING_REFINEMENT_JUSTIFIED."""
    report = _run(tmp_path)
    summary = report["summary"]

    assert summary["review_outcome"] == "BOUNDED_COUPLING_REFINEMENT_JUSTIFIED"
    assert summary["coupling_defect"] == "REVISED_DEF_FIRES_WITHOUT_CORRESPONDING_BLOCKER_ARTIFACT_FLUX_IN_LEDGER"
    assert summary["coupling_boundedness"] == "COUPLING_DEFECT_IS_SPECIFIC_AND_BOUNDED_BETWEEN_SEAM_AND_BLOCKER_ARTIFACT"
    assert summary["routing_decision"] == "BOUNDED_COUPLING_REFINEMENT_JUSTIFIED_SEAM_ARTIFACT_BINDING_REVIEW"
    assert summary["coupling_disposition"] == "REFINE_COUPLING"
    assert summary["next_action"] == "EXECUTE_BOUNDED_COUPLING_REFINEMENT_PACKET_ONCE"
    assert summary["no_loop_rule"] == "ONE_AUTHORITY_COUPLING_REVIEW_ONLY"


def test_not_bounded_coupling_escalate_path(tmp_path: Path) -> None:
    """When Q2=not-bounded, outcome must be COUPLING_DEFECT_NOT_SUFFICIENTLY_BOUNDED."""
    report = _run(
        tmp_path,
        q2_answer="COUPLING_DEFECT_NOT_SUFFICIENTLY_BOUNDED_APPEARS_SYSTEMIC",
    )
    summary = report["summary"]

    assert summary["review_outcome"] == "COUPLING_DEFECT_NOT_SUFFICIENTLY_BOUNDED"
    assert summary["coupling_disposition"] == "ESCALATE"
    assert summary["next_action"] == "ESCALATE_TO_THEORY_POSTURE_OR_PROGRAM_PAUSE_REVIEW"


def test_bounded_but_hold_path(tmp_path: Path) -> None:
    """When Q2=bounded but Q3=hold, outcome must be COUPLING_DEFECT_BOUNDED_BUT_HOLD."""
    report = _run(
        tmp_path,
        q3_answer="HOLD_SECONDARY_AND_STOP_AWAITING_THEORY_ADVANCE",
    )
    summary = report["summary"]

    assert summary["review_outcome"] == "COUPLING_DEFECT_BOUNDED_BUT_HOLD_AWAITING_THEORY"
    assert summary["coupling_disposition"] == "HOLD_THEORY"
    assert summary["next_action"] == "HOLD_REVISED_DEF_SECONDARY_AWAIT_THEORY_ADVANCE"
