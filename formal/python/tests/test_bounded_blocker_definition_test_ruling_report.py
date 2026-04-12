from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import bounded_blocker_definition_test_ruling_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _seed(
    tmp_path: Path,
    *,
    execution_classification: str = "EXECUTION_VALID_REVISED_DEF_FIRES_AUTHORITATIVE_BLOCKED",
    revised_blocker_def_fires: bool = True,
    blocker_signal: str = "REVISED_DEF_ONLY",
) -> tuple[Path, object]:
    """Return (declaration_path, original_repo_root)."""
    reports_dir = tmp_path / "formal" / "output" / "reports"
    reports_dir.mkdir(parents=True, exist_ok=True)

    execution_path = reports_dir / "bounded_blocker_definition_test_execution_20260411_v0.json"
    _write_json(
        execution_path,
        {
            "summary": {
                "execution_classification": execution_classification,
                "revised_blocker_def_fires": revised_blocker_def_fires,
                "authoritative_fires": False,
                "blocker_signal": blocker_signal,
                "candidate_blocker_definition": "REVISED_BLOCKER_DEF_SEAM_ROW_STATE_TRANSITION_WITH_TRANSPORT_COHERENCE_CHECK",
                "retained_authoritative_signal": "BLOCKER_TOKEN_CHANGE_REMAINS_AUTHORITATIVE",
                "target_row_id": "ROW-SEAM-QM-STAT-001",
                "no_loop_rule": "ONE_BOUNDED_BLOCKER_DEFINITION_TEST_EXECUTION_ONLY",
                "next_action": "EMIT_BOUNDED_BLOCKER_DEFINITION_TEST_RULING",
            }
        },
    )

    declaration_path = (
        tmp_path / "formal" / "docs" / "release"
        / "BOUNDED_BLOCKER_DEFINITION_TEST_RULING_20260411_v0.json"
    )
    declaration_path.parent.mkdir(parents=True, exist_ok=True)

    _write_json(
        declaration_path,
        {
            "schema_id": "BOUNDED_BLOCKER_DEFINITION_TEST_RULING_20260411_v0",
            "required_inputs": {
                "bounded_blocker_definition_test_execution_report": "formal/output/reports/bounded_blocker_definition_test_execution_20260411_v0.json",
            },
            "ruling_outcomes": [
                {
                    "outcome_id": "OUTCOME_1",
                    "outcome": "REVISED_BLOCKER_DEF_REVEALS_MEANINGFUL_MOVEMENT",
                    "activation_condition": "REVISED_DEF_FIRES_AND_DEMONSTRATES_TIGHTER_COUPLING_THAN_DIAGNOSTIC_SIGNAL",
                },
                {
                    "outcome_id": "OUTCOME_2",
                    "outcome": "REVISED_BLOCKER_DEF_VALID_BUT_NONMOVING",
                    "activation_condition": "REVISED_DEF_FIRES_BUT_DOES_NOT_EXCEED_DIAGNOSTIC_SIGNAL_RIGOR",
                },
                {
                    "outcome_id": "OUTCOME_3",
                    "outcome": "REVISED_BLOCKER_DEF_NOT_FIT_FOR_AUTHORITY_USE",
                    "activation_condition": "REVISED_DEF_DOES_NOT_FIRE_OR_FIRES_INCONSISTENTLY",
                },
            ],
            "ruling_policy": {
                "promotion_requires_both_signals_still": False,
                "promotion_requires_revised_def_fires_decisively": True,
                "promotion_requires_tighter_coupling_than_diagnostic": True,
                "authoritative_still_blocked_in_this_evaluation": True,
                "default_ruling": "REVISED_BLOCKER_DEF_VALID_BUT_NONMOVING",
                "no_loop_rule": "ONE_BOUNDED_BLOCKER_DEFINITION_TEST_RULING_ONLY",
                "no_further_blocker_def_tests_until_defect_resolved_policy": True,
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


def test_ruling_valid_but_nonmoving_when_revised_def_fires(tmp_path: Path) -> None:
    """When revised def fires validly but no explicit tighter coupling, ruling is VALID_BUT_NONMOVING."""
    report = _run(tmp_path)
    summary = report["summary"]

    assert summary["test_ruling"] == "REVISED_BLOCKER_DEF_VALID_BUT_NONMOVING"
    assert summary["revised_blocker_def_fires"] is True
    assert summary["authoritative_fires"] is False
    assert summary["blocker_signal"] == "REVISED_DEF_ONLY"
    assert summary["candidate_blocker_definition"] == "REVISED_BLOCKER_DEF_SEAM_ROW_STATE_TRANSITION_WITH_TRANSPORT_COHERENCE_CHECK"
    assert summary["no_loop_rule"] == "ONE_BOUNDED_BLOCKER_DEFINITION_TEST_RULING_ONLY"
    assert summary["next_action"] == "ASSESS_BLOCKER_DEFINITION_TEST_RULING_AND_DECIDE_PROMOTION_OR_HOLD"


def test_ruling_not_fit_when_revised_def_does_not_fire(tmp_path: Path) -> None:
    """When revised def does not fire, ruling must be NOT_FIT_FOR_AUTHORITY_USE."""
    report = _run(
        tmp_path,
        execution_classification="EXECUTION_VALID_NO_SIGNALS_FIRE",
        revised_blocker_def_fires=False,
        blocker_signal="NONE",
    )
    summary = report["summary"]

    assert summary["test_ruling"] == "REVISED_BLOCKER_DEF_NOT_FIT_FOR_AUTHORITY_USE"
    assert summary["revised_blocker_def_fires"] is False
    assert summary["blocker_signal"] == "NONE"
