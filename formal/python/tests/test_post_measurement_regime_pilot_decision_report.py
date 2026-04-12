from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.tools import post_measurement_regime_pilot_decision_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _seed_inputs(
    tmp_path: Path,
    *,
    pilot_ruling: str,
    new_signal_fired: bool = True,
    retained_signal_fired: bool = False,
    specific_authority_coupling_defect_identified: bool = False,
    bounded_coupling_refinement_packet: str | None = None,
) -> tuple[Path, Path, Path]:
    """Return (declaration_path, ruling_report_path, execution_report_path)."""
    ruling_dir = tmp_path / "formal" / "output" / "reports"
    ruling_dir.mkdir(parents=True, exist_ok=True)

    ruling_path = ruling_dir / "bounded_measurement_regime_pilot_ruling_20260411_v0.json"
    execution_path = ruling_dir / "bounded_measurement_regime_pilot_execution_20260411_v0.json"

    _write_json(
        ruling_path,
        {
            "summary": {
                "pilot_ruling": pilot_ruling,
                "execution_classification": "PILOT_VALID_BUT_NONMOVING",
                "new_signal_fired": new_signal_fired,
                "retained_signal_fired": retained_signal_fired,
                "blocker_movement_signal": "NEW_SIGNAL_ONLY" if new_signal_fired else "NONE",
                "no_loop_rule": "ONE_BOUNDED_MEASUREMENT_REGIME_PILOT_ONLY",
                "next_action": "ASSESS_PILOT_RESULT_AND_DECIDE_ROLLBACK_OR_HOLD",
            }
        },
    )

    _write_json(
        execution_path,
        {
            "summary": {
                "execution_classification": "PILOT_VALID_BUT_NONMOVING",
                "new_signal_fired": new_signal_fired,
                "retained_signal_fired": retained_signal_fired,
                "blocker_movement_signal": "NEW_SIGNAL_ONLY" if new_signal_fired else "NONE",
                "no_loop_rule": "ONE_BOUNDED_MEASUREMENT_REGIME_PILOT_ONLY",
                "next_action": "EMIT_BOUNDED_MEASUREMENT_REGIME_PILOT_RULING",
            }
        },
    )

    declaration_path = (
        tmp_path / "formal" / "docs" / "release"
        / "POST_MEASUREMENT_REGIME_PILOT_DECISION_20260411_v0.json"
    )
    declaration_path.parent.mkdir(parents=True, exist_ok=True)

    _write_json(
        declaration_path,
        {
            "schema_id": "POST_MEASUREMENT_REGIME_PILOT_DECISION_20260411_v0",
            "current_pilot_ruling": pilot_ruling,
            "required_inputs": {
                "bounded_measurement_regime_pilot_ruling_report": "formal/output/reports/bounded_measurement_regime_pilot_ruling_20260411_v0.json",
                "bounded_measurement_regime_pilot_execution_report": "formal/output/reports/bounded_measurement_regime_pilot_execution_20260411_v0.json",
            },
            "candidate_routes": [
                {"route_id": "ROLL_BACK_ROUTE", "next_action": "DEPRECATE_REVISED_SIGNAL_AND_RESTORE_PRIOR_REGIME"},
                {"route_id": "RETAIN_DIAGNOSTIC_ROUTE", "next_action": "REGISTER_REVISED_SIGNAL_AS_DIAGNOSTIC_ONLY_AND_HOLD"},
                {"route_id": "AUTHORITY_COUPLING_REFINEMENT_ROUTE", "next_action": "EXECUTE_AUTHORITY_COUPLING_REFINEMENT_PACKET_ONCE"},
            ],
            "decision_policy": {
                "specific_authority_coupling_defect_identified": specific_authority_coupling_defect_identified,
                "specific_authority_coupling_defect_note": None,
                "bounded_coupling_refinement_packet": bounded_coupling_refinement_packet,
                "default_decision": "RETAIN_REVISED_SIGNAL_AS_DIAGNOSTIC_ONLY",
                "no_loop_rule": "ONE_POST_PILOT_DECISION_ONLY",
                "no_further_pilot_loops_policy": "NO_FURTHER_MEASUREMENT_REGIME_PILOT_LOOPS_UNTIL_DECISION_RESOLVED",
            },
        },
    )

    # Patch REPO_ROOT temporarily so the tool resolves paths from tmp_path
    original_repo_root = tool.REPO_ROOT
    tool.REPO_ROOT = tmp_path
    return declaration_path, ruling_path, execution_path, original_repo_root


@pytest.fixture(autouse=True)
def _patch_repo_root(request, monkeypatch):
    """Each test passes its own tmp_path and handles patching inline via _seed_inputs."""
    yield


def _run(tmp_path: Path, **seed_kwargs) -> dict:
    declaration_path, _, _, original = _seed_inputs(tmp_path, **seed_kwargs)
    try:
        report = tool.build_report(
            declaration_path=declaration_path,
            captured_at_utc="2026-04-11T00:00:00Z",
        )
    finally:
        tool.REPO_ROOT = original
    return report


def test_default_retain_diagnostic_path(tmp_path: Path) -> None:
    """When ruling is VALID_BUT_NONMOVING and no coupling defect, default to RETAIN_REVISED_SIGNAL_AS_DIAGNOSTIC_ONLY."""
    report = _run(
        tmp_path,
        pilot_ruling="REVISED_SIGNAL_VALID_BUT_NONMOVING",
        new_signal_fired=True,
        retained_signal_fired=False,
        specific_authority_coupling_defect_identified=False,
        bounded_coupling_refinement_packet=None,
    )
    summary = report["summary"]

    assert summary["post_pilot_decision"] == "RETAIN_REVISED_SIGNAL_AS_DIAGNOSTIC_ONLY"
    assert summary["revised_signal_disposition"] == "RETAIN_DIAGNOSTIC"
    assert summary["next_action"] == "REGISTER_REVISED_SIGNAL_AS_DIAGNOSTIC_ONLY_AND_HOLD"
    assert summary["no_loop_rule"] == "ONE_POST_PILOT_DECISION_ONLY"
    assert summary["new_signal_fired"] is True
    assert summary["retained_signal_fired"] is False


def test_rollback_path(tmp_path: Path) -> None:
    """When ruling is NOT_FIT_FOR_PROMOTION_USE, decision must be ROLL_BACK_REVISED_SIGNAL_FOR_PROMOTION_USE."""
    report = _run(
        tmp_path,
        pilot_ruling="REVISED_SIGNAL_NOT_FIT_FOR_PROMOTION_USE",
        new_signal_fired=False,
        retained_signal_fired=False,
        specific_authority_coupling_defect_identified=False,
        bounded_coupling_refinement_packet=None,
    )
    summary = report["summary"]

    assert summary["post_pilot_decision"] == "ROLL_BACK_REVISED_SIGNAL_FOR_PROMOTION_USE"
    assert summary["revised_signal_disposition"] == "ROLL_BACK"
    assert summary["next_action"] == "DEPRECATE_REVISED_SIGNAL_AND_RESTORE_PRIOR_REGIME"
    assert summary["no_loop_rule"] == "ONE_POST_PILOT_DECISION_ONLY"
