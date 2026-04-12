from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import post_posture_review_program_mode_transition_report as transition_tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    measurement_defect_answer: str,
    new_signal_answer: str,
    retained_signal_answer: str,
    pilot_tranche_answer: str,
) -> None:
    _write_json(
        path,
        {
            "triggered_by": "PROGRAM_POSTURE_REVIEW_PACKET_MATERIALIZED",
            "selected_next_program_mode": "REORIENT_MEASUREMENT_REGIME",
            "required_inputs": {
                "program_posture_review_packet_report": "formal/output/reports/program_posture_review_packet_20260411_v0.json",
            },
            "transition_questions": [],
            "transition_policy": {
                "measurement_defect_answer": measurement_defect_answer,
                "new_signal_answer": new_signal_answer,
                "retained_signal_answer": retained_signal_answer,
                "pilot_tranche_answer": pilot_tranche_answer,
                "no_loop_rule": "ONE_BOUNDED_MEASUREMENT_REGIME_PILOT_ONLY",
                "no_broad_rewrite_policy": "PILOT_BOUNDED_SINGLE_TRANCHE_BEFORE_REGIME_PROMOTION",
                "reversibility_rule": "PILOT_RESULTS_MUST_BE_ASSESSED_BEFORE_PROMOTION_OR_ROLLBACK",
            },
        },
    )


def _write_posture_review_report(reports_dir: Path, *, outcome: str, selected_mode: str) -> None:
    _write_json(
        reports_dir / "program_posture_review_packet_20260411_v0.json",
        {
            "summary": {
                "packet_outcome": outcome,
                "measurement_regime_fit_for_purpose": False,
                "formal_organization_outpacing_conversion": True,
                "selected_next_program_mode": selected_mode,
                "no_loop_rule": "ONE_POSTURE_REVIEW_ONLY",
                "next_action": "EXECUTE_POST_POSTURE_REVIEW_PROGRAM_MODE_TRANSITION",
            }
        },
    )


def test_transition_materializes_with_valid_policy_answers(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(transition_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "POST_POSTURE_REVIEW_PROGRAM_MODE_TRANSITION_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_declaration(
        declaration_path,
        measurement_defect_answer="BLOCKER_MOVEMENT_SIGNALS_NEVER_TRIGGERED_UNDER_ANY_ATTACK_CLASS",
        new_signal_answer="SEAM_INTEGRATION_COVERAGE_DELTA_GT_0",
        retained_signal_answer="BLOCKER_TOKEN_CHANGE_REMAINS_AUTHORITATIVE",
        pilot_tranche_answer="ONE_SEAM_ROW_RECOMPUTE_UNDER_REVISED_SIGNALS",
    )
    _write_posture_review_report(
        reports_dir,
        outcome="PROGRAM_POSTURE_REVIEW_PACKET_MATERIALIZED",
        selected_mode="REORIENT_MEASUREMENT_REGIME",
    )

    report = transition_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["transition_outcome"] == "MEASUREMENT_REGIME_TRANSITION_MATERIALIZED"
    assert (
        report["summary"]["measurement_defect"]
        == "BLOCKER_MOVEMENT_SIGNALS_NEVER_TRIGGERED_UNDER_ANY_ATTACK_CLASS"
    )
    assert report["summary"]["new_blocker_movement_signal"] == "SEAM_INTEGRATION_COVERAGE_DELTA_GT_0"
    assert report["summary"]["retained_blocker_movement_signal"] == "BLOCKER_TOKEN_CHANGE_REMAINS_AUTHORITATIVE"
    assert report["summary"]["pilot_tranche"] == "ONE_SEAM_ROW_RECOMPUTE_UNDER_REVISED_SIGNALS"
    assert report["summary"]["no_loop_rule"] == "ONE_BOUNDED_MEASUREMENT_REGIME_PILOT_ONLY"
    assert report["summary"]["next_action"] == "EXECUTE_BOUNDED_MEASUREMENT_REGIME_PILOT_ONCE"
    assert report["criteria"]["reversibility_rule_declared"] is True
    assert report["criteria"]["bounded_single_tranche_policy_declared"] is True


def test_transition_incomplete_when_posture_mode_is_not_reorient_measurement_regime(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(transition_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "POST_POSTURE_REVIEW_PROGRAM_MODE_TRANSITION_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_declaration(
        declaration_path,
        measurement_defect_answer="BLOCKER_MOVEMENT_SIGNALS_NEVER_TRIGGERED_UNDER_ANY_ATTACK_CLASS",
        new_signal_answer="SEAM_INTEGRATION_COVERAGE_DELTA_GT_0",
        retained_signal_answer="BLOCKER_TOKEN_CHANGE_REMAINS_AUTHORITATIVE",
        pilot_tranche_answer="ONE_SEAM_ROW_RECOMPUTE_UNDER_REVISED_SIGNALS",
    )
    _write_posture_review_report(
        reports_dir,
        outcome="PROGRAM_POSTURE_REVIEW_PACKET_MATERIALIZED",
        selected_mode="REORIENT_ARCHITECTURE_TARGET_SELECTION",
    )

    report = transition_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["transition_outcome"] == "MEASUREMENT_REGIME_TRANSITION_INCOMPLETE"
    assert report["summary"]["next_action"] == "RESTORE_TRANSITION_PRECONDITIONS"
    assert report["criteria"]["transition_triggered"] is False
