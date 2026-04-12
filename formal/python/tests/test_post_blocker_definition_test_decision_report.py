from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.tools import post_blocker_definition_test_decision_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _seed_inputs(
    tmp_path: Path,
    *,
    test_ruling: str,
    revised_blocker_def_fires: bool = True,
    specific_authority_coupling_defect_identified: bool = False,
    authority_coupling_refinement_packet: str | None = None,
) -> tuple[Path, Path]:
    """Return (declaration_path, original_repo_root)."""
    reports_dir = tmp_path / "formal" / "output" / "reports"
    reports_dir.mkdir(parents=True, exist_ok=True)

    ruling_path = reports_dir / "bounded_blocker_definition_test_ruling_20260411_v0.json"
    _write_json(
        ruling_path,
        {
            "summary": {
                "test_ruling": test_ruling,
                "revised_blocker_def_fires": revised_blocker_def_fires,
                "authoritative_fires": False,
                "blocker_signal": "REVISED_DEF_ONLY" if revised_blocker_def_fires else "NONE",
                "candidate_blocker_definition": "REVISED_BLOCKER_DEF_SEAM_ROW_STATE_TRANSITION_WITH_TRANSPORT_COHERENCE_CHECK",
                "no_loop_rule": "ONE_BOUNDED_BLOCKER_DEFINITION_TEST_RULING_ONLY",
                "next_action": "ASSESS_BLOCKER_DEFINITION_TEST_RULING_AND_DECIDE_PROMOTION_OR_HOLD",
            }
        },
    )

    declaration_path = (
        tmp_path / "formal" / "docs" / "release"
        / "POST_BLOCKER_DEFINITION_TEST_DECISION_20260411_v0.json"
    )
    declaration_path.parent.mkdir(parents=True, exist_ok=True)

    _write_json(
        declaration_path,
        {
            "schema_id": "POST_BLOCKER_DEFINITION_TEST_DECISION_20260411_v0",
            "required_inputs": {
                "bounded_blocker_definition_test_ruling_report": "formal/output/reports/bounded_blocker_definition_test_ruling_20260411_v0.json",
            },
            "test_result_summary": {
                "test_ruling": test_ruling,
                "revised_blocker_def_fires": revised_blocker_def_fires,
                "authoritative_fires": False,
                "interpretation": "Revised blocker definition is stronger but still not authoritative.",
            },
            "candidate_routes": [
                {
                    "route_id": "HOLD_ROUTE",
                    "route_name": "HOLD_REVISED_BLOCKER_DEF_AS_SECONDARY_REQUIRE_AUTHORITY_COUPLING_REVIEW",
                    "next_action": "REQUIRE_ONE_BOUNDED_AUTHORITY_COUPLING_REVIEW",
                },
                {
                    "route_id": "COUPLING_REFINEMENT_ROUTE",
                    "route_name": "EXECUTE_AUTHORITY_COUPLING_REFINEMENT_BOUNDED_ONCE",
                    "next_action": "EXECUTE_AUTHORITY_COUPLING_REFINEMENT_PACKET_ONCE",
                },
                {
                    "route_id": "ESCALATE_ROUTE",
                    "route_name": "ESCALATE_TO_THEORY_POSTURE_OR_PROGRAM_PAUSE_REVIEW",
                    "next_action": "ESCALATE_TO_THEORY_POSTURE_OR_PROGRAM_PAUSE_REVIEW",
                },
            ],
            "decision_policy": {
                "specific_authority_coupling_defect_identified": specific_authority_coupling_defect_identified,
                "specific_authority_coupling_defect_note": None,
                "authority_coupling_refinement_packet": authority_coupling_refinement_packet,
                "default_decision": "HOLD_REVISED_BLOCKER_DEF_AS_SECONDARY_REQUIRE_AUTHORITY_COUPLING_REVIEW",
                "default_next_action": "REQUIRE_ONE_BOUNDED_AUTHORITY_COUPLING_REVIEW",
                "no_loop_rule": "ONE_POST_BLOCKER_DEFINITION_TEST_DECISION_ONLY",
                "no_further_blocker_definition_testing_until_routing_resolved": True,
            },
        },
    )

    original = tool.REPO_ROOT
    tool.REPO_ROOT = tmp_path
    return declaration_path, original


def _run(tmp_path: Path, **seed_kwargs) -> dict:
    declaration_path, original = _seed_inputs(tmp_path, **seed_kwargs)
    try:
        return tool.build_report(
            declaration_path=declaration_path,
            captured_at_utc="2026-04-11T00:00:00Z",
        )
    finally:
        tool.REPO_ROOT = original


def test_default_hold_path_when_valid_but_nonmoving(tmp_path: Path) -> None:
    """When ruling is VALID_BUT_NONMOVING and no coupling defect, decision must be HOLD."""
    report = _run(
        tmp_path,
        test_ruling="REVISED_BLOCKER_DEF_VALID_BUT_NONMOVING",
        revised_blocker_def_fires=True,
        specific_authority_coupling_defect_identified=False,
        authority_coupling_refinement_packet=None,
    )
    summary = report["summary"]

    assert summary["post_test_decision"] == "HOLD_REVISED_BLOCKER_DEF_AS_SECONDARY_REQUIRE_AUTHORITY_COUPLING_REVIEW"
    assert summary["revised_signal_disposition"] == "HOLD_SECONDARY"
    assert summary["test_ruling"] == "REVISED_BLOCKER_DEF_VALID_BUT_NONMOVING"
    assert summary["revised_blocker_def_fires"] is True
    assert summary["authoritative_fires"] is False
    assert summary["no_loop_rule"] == "ONE_POST_BLOCKER_DEFINITION_TEST_DECISION_ONLY"
    assert summary["no_further_blocker_testing_until_routing_resolved"] is True
    assert summary["next_action"] == "REQUIRE_ONE_BOUNDED_AUTHORITY_COUPLING_REVIEW"


def test_escalate_path_when_not_fit(tmp_path: Path) -> None:
    """When ruling is NOT_FIT_FOR_AUTHORITY_USE, decision must escalate."""
    report = _run(
        tmp_path,
        test_ruling="REVISED_BLOCKER_DEF_NOT_FIT_FOR_AUTHORITY_USE",
        revised_blocker_def_fires=False,
        specific_authority_coupling_defect_identified=False,
        authority_coupling_refinement_packet=None,
    )
    summary = report["summary"]

    assert summary["post_test_decision"] == "ESCALATE_TO_THEORY_POSTURE_OR_PROGRAM_PAUSE_REVIEW"
    assert summary["revised_signal_disposition"] == "ESCALATE"
    assert summary["test_ruling"] == "REVISED_BLOCKER_DEF_NOT_FIT_FOR_AUTHORITY_USE"
    assert summary["revised_blocker_def_fires"] is False
    assert summary["next_action"] == "ESCALATE_TO_THEORY_POSTURE_OR_PROGRAM_PAUSE_REVIEW"
