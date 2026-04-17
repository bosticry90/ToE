from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import seam_resolution_sla_ledger_generate as tool


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def test_seam_resolution_sla_ledger_builds_expected_states(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(tool, "COMPLETION_MATRIX_PATH", tmp_path / "formal" / "docs" / "release" / "TOE_GLOBAL_COMPLETION_MATRIX_v0.md")
    monkeypatch.setattr(tool, "DASHBOARD_REPORT_PATH", tmp_path / "formal" / "output" / "reports" / "blocker_burn_dashboard_20260416_v0.json")
    monkeypatch.setattr(tool, "HOLD_POLICY_PATH", tmp_path / "formal" / "docs" / "release" / "WS_10_PACKET41_PACKET42_HOLD_RECONSIDERATION_POLICY_20260408_v0.md")
    monkeypatch.setattr(tool, "CLOSURE_OWNER_MAP_PATH", tmp_path / "formal" / "docs" / "release" / "GOVERNANCE_AUDIT_PACKET_CLOSURE_OWNER_MAP_20260410_v0.json")
    monkeypatch.setattr(tool, "SEAM_INVENTORY_PATH", tmp_path / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md")

    _write_text(
        tool.COMPLETION_MATRIX_PATH,
        "| row_id | domain | lane | current_status | blocker_class | primary_target | primary_artifact | primary_gate |\n| --- | --- | --- | --- | --- | --- | --- | --- |\n| ROW-SEAM-QM-STAT-001 | seam | LANE_A | NEXT_BOUNDED | SEAM_INTEGRATION_GAP | a | b | c |\n| ROW-SEAM-GR-QM-001 | seam | LANE_B | COMPLETE | PARITY_DRIFT | a | b | c |\n",
    )
    _write_json(tool.DASHBOARD_REPORT_PATH, {"blocker_scoreboard": {"movement_status": "FLAT", "net_delta": 0, "exception_required": True}, "source_freshness": {"stale_input_warning": True}})
    _write_text(
        tool.HOLD_POLICY_PATH,
        "Decision owner: WS-10 lane authority owner.\nReview cadence: every 24 hours while lane remains active.\nEscalation window: if state does not transition after two consecutive review windows, require explicit branch decision artifact in release surfaces.\n",
    )
    _write_text(
        tool.SEAM_INVENTORY_PATH,
        "| seam_id | class | seam_class_token | witness_route_status | source_artifacts | promotion_candidate |\n| --- | --- | --- | --- | --- | --- |\n| SEAM-QM-STAT | B | TOE_CK_CLASS_COMPATIBILITY_v0 | COUNTERFACTUAL_BUNDLE_PINNED_v0 | qm | NO |\n| SEAM-GR-QM | A | TOE_CK_CLASS_THEOREM_LINKED_v0 | CLASS_A_PROMOTED_CYCLE03_v0 | gr,qm | NO |\n\n| seam_id | governance_complete | physics_complete | status_read |\n| --- | --- | --- | --- |\n| SEAM-QM-STAT | NO | NO | CLASS_B_TRACKED_NOT_GOVERNANCE_COMPLETE_NOT_PHYSICS_COMPLETE |\n| SEAM-GR-QM | YES | YES | GOVERNANCE_COMPLETE_AND_PHYSICS_COMPLETE |\n",
    )
    _write_json(
        tool.CLOSURE_OWNER_MAP_PATH,
        {
            "rows": [
                {
                    "row_id": "ROW-SEAM-QM-STAT-001",
                    "primary_owner": "TEAM_A",
                    "secondary_owner": "TEAM_GOV",
                    "required_evidence_surface": "evidence/a.md",
                    "exit_criterion": "EXIT_A",
                },
                {
                    "row_id": "ROW-SEAM-GR-QM-001",
                    "primary_owner": "TEAM_B",
                    "secondary_owner": "TEAM_GOV",
                    "required_evidence_surface": "evidence/b.md",
                    "exit_criterion": "EXIT_B",
                },
            ]
        },
    )

    report = tool.build_seam_sla_ledger(output_path=tmp_path / "out.json", captured_at_utc="2026-04-16T00:00:00Z")
    assert report["summary"]["seam_rows_total"] == 2
    assert report["summary"]["active_review_rows"] == 1
    assert report["summary"]["held_review_rows"] == 1
    assert report["summary"]["missing_owner_rows"] == []
    assert report["summary"]["owner_completion_rate"] == 1.0
    assert report["summary"]["missing_seam_status_rows"] == []
    assert report["summary"]["seam_status_coverage_rate"] == 1.0
    assert report["policy"]["decision_owner_assignment_status"] == "NAMED_OWNERS_ASSIGNED"
    states = {entry["row_id"]: entry["decision_state"] for entry in report["entries"]}
    assert states["ROW-SEAM-QM-STAT-001"] == "HOLD_RETAINED_PENDING_BRANCH_EXCEPTION_DECISION"
    assert states["ROW-SEAM-GR-QM-001"] == "HOLD_RETAINED_PARITY_RESTORE_REQUIRED"
    owners = {entry["row_id"]: entry["primary_owner"] for entry in report["entries"]}
    assert owners["ROW-SEAM-QM-STAT-001"] == "TEAM_A"
    assert owners["ROW-SEAM-GR-QM-001"] == "TEAM_B"
    evidence = {entry["row_id"]: entry["required_evidence_surface"] for entry in report["entries"]}
    assert evidence["ROW-SEAM-QM-STAT-001"] == "evidence/a.md"
    seam_meta = {entry["row_id"]: entry for entry in report["entries"]}
    assert seam_meta["ROW-SEAM-QM-STAT-001"]["seam_id"] == "SEAM-QM-STAT"
    assert seam_meta["ROW-SEAM-QM-STAT-001"]["seam_class"] == "B"
    assert seam_meta["ROW-SEAM-QM-STAT-001"]["governance_complete"] is False
    assert seam_meta["ROW-SEAM-GR-QM-001"]["physics_complete"] is True
    assert seam_meta["ROW-SEAM-GR-QM-001"]["seam_status_resolution"] == "CANONICAL_SEAM_STATUS_PINNED"


def test_seam_resolution_sla_ledger_uses_decreasing_signal_for_review_eligibility(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(tool, "COMPLETION_MATRIX_PATH", tmp_path / "formal" / "docs" / "release" / "TOE_GLOBAL_COMPLETION_MATRIX_v0.md")
    monkeypatch.setattr(tool, "DASHBOARD_REPORT_PATH", tmp_path / "formal" / "output" / "reports" / "blocker_burn_dashboard_20260416_v0.json")
    monkeypatch.setattr(tool, "HOLD_POLICY_PATH", tmp_path / "formal" / "docs" / "release" / "WS_10_PACKET41_PACKET42_HOLD_RECONSIDERATION_POLICY_20260408_v0.md")
    monkeypatch.setattr(tool, "CLOSURE_OWNER_MAP_PATH", tmp_path / "formal" / "docs" / "release" / "GOVERNANCE_AUDIT_PACKET_CLOSURE_OWNER_MAP_20260410_v0.json")
    monkeypatch.setattr(tool, "SEAM_INVENTORY_PATH", tmp_path / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md")

    _write_text(
        tool.COMPLETION_MATRIX_PATH,
        "| row_id | domain | lane | current_status | blocker_class | primary_target | primary_artifact | primary_gate |\n| --- | --- | --- | --- | --- | --- | --- | --- |\n| ROW-SEAM-QM-STAT-001 | seam | LANE_A | NEXT_BOUNDED | SEAM_INTEGRATION_GAP | a | b | c |\n",
    )
    _write_json(tool.DASHBOARD_REPORT_PATH, {"blocker_scoreboard": {"movement_status": "DECREASING", "net_delta": -1, "exception_required": False}, "source_freshness": {"stale_input_warning": False}})
    _write_text(
        tool.HOLD_POLICY_PATH,
        "Decision owner: WS-10 lane authority owner.\nReview cadence: every 24 hours while lane remains active.\nEscalation window: if state does not transition after two consecutive review windows, require explicit branch decision artifact in release surfaces.\n",
    )
    _write_text(
        tool.SEAM_INVENTORY_PATH,
        "| seam_id | class | seam_class_token | witness_route_status | source_artifacts | promotion_candidate |\n| --- | --- | --- | --- | --- | --- |\n| SEAM-QM-STAT | B | TOE_CK_CLASS_COMPATIBILITY_v0 | COUNTERFACTUAL_BUNDLE_PINNED_v0 | qm | NO |\n\n| seam_id | governance_complete | physics_complete | status_read |\n| --- | --- | --- | --- |\n| SEAM-QM-STAT | NO | NO | CLASS_B_TRACKED_NOT_GOVERNANCE_COMPLETE_NOT_PHYSICS_COMPLETE |\n",
    )
    _write_json(
        tool.CLOSURE_OWNER_MAP_PATH,
        {
            "rows": [
                {
                    "row_id": "ROW-SEAM-QM-STAT-001",
                    "primary_owner": "TEAM_A",
                    "secondary_owner": "TEAM_GOV",
                    "required_evidence_surface": "evidence/a.md",
                    "exit_criterion": "EXIT_A",
                }
            ]
        },
    )

    report = tool.build_seam_sla_ledger(output_path=tmp_path / "out.json", captured_at_utc=None)
    assert report["entries"][0]["decision_state"] == "BOUNDED_CONTINUATION_REVIEW_ELIGIBLE"
    assert report["entries"][0]["primary_owner"] == "TEAM_A"
    assert report["entries"][0]["seam_status_resolution"] == "CANONICAL_SEAM_STATUS_PINNED"


def test_seam_resolution_sla_ledger_tracks_missing_owner_rows(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(tool, "COMPLETION_MATRIX_PATH", tmp_path / "formal" / "docs" / "release" / "TOE_GLOBAL_COMPLETION_MATRIX_v0.md")
    monkeypatch.setattr(tool, "DASHBOARD_REPORT_PATH", tmp_path / "formal" / "output" / "reports" / "blocker_burn_dashboard_20260416_v0.json")
    monkeypatch.setattr(tool, "HOLD_POLICY_PATH", tmp_path / "formal" / "docs" / "release" / "WS_10_PACKET41_PACKET42_HOLD_RECONSIDERATION_POLICY_20260408_v0.md")
    monkeypatch.setattr(tool, "CLOSURE_OWNER_MAP_PATH", tmp_path / "formal" / "docs" / "release" / "GOVERNANCE_AUDIT_PACKET_CLOSURE_OWNER_MAP_20260410_v0.json")
    monkeypatch.setattr(tool, "SEAM_INVENTORY_PATH", tmp_path / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md")

    _write_text(
        tool.COMPLETION_MATRIX_PATH,
        "| row_id | domain | lane | current_status | blocker_class | primary_target | primary_artifact | primary_gate |\n| --- | --- | --- | --- | --- | --- | --- | --- |\n| ROW-SEAM-QM-STAT-001 | seam | LANE_A | NEXT_BOUNDED | SEAM_INTEGRATION_GAP | a | b | c |\n| ROW-SEAM-QFT-GR-001 | seam | LANE_B | NEXT_BOUNDED | SEAM_INTEGRATION_GAP | a | b | c |\n",
    )
    _write_json(tool.DASHBOARD_REPORT_PATH, {"blocker_scoreboard": {"movement_status": "FLAT", "net_delta": 0, "exception_required": True}, "source_freshness": {"stale_input_warning": False}})
    _write_text(
        tool.HOLD_POLICY_PATH,
        "Decision owner: WS-10 lane authority owner.\nReview cadence: every 24 hours while lane remains active.\nEscalation window: if state does not transition after two consecutive review windows, require explicit branch decision artifact in release surfaces.\n",
    )
    _write_text(
        tool.SEAM_INVENTORY_PATH,
        "| seam_id | class | seam_class_token | witness_route_status | source_artifacts | promotion_candidate |\n| --- | --- | --- | --- | --- | --- |\n| SEAM-QM-STAT | B | TOE_CK_CLASS_COMPATIBILITY_v0 | COUNTERFACTUAL_BUNDLE_PINNED_v0 | qm | NO |\n\n| seam_id | governance_complete | physics_complete | status_read |\n| --- | --- | --- | --- |\n| SEAM-QM-STAT | NO | NO | CLASS_B_TRACKED_NOT_GOVERNANCE_COMPLETE_NOT_PHYSICS_COMPLETE |\n",
    )
    _write_json(
        tool.CLOSURE_OWNER_MAP_PATH,
        {
            "rows": [
                {
                    "row_id": "ROW-SEAM-QM-STAT-001",
                    "primary_owner": "TEAM_A",
                    "secondary_owner": "TEAM_GOV",
                    "required_evidence_surface": "evidence/a.md",
                    "exit_criterion": "EXIT_A",
                }
            ]
        },
    )

    report = tool.build_seam_sla_ledger(output_path=tmp_path / "out.json", captured_at_utc="2026-04-16T00:00:00Z")
    assert report["summary"]["missing_owner_rows"] == ["ROW-SEAM-QFT-GR-001"]
    assert report["summary"]["owner_completion_rate"] == 0.5
    assert report["summary"]["missing_seam_status_rows"] == ["ROW-SEAM-QFT-GR-001"]
    assert report["summary"]["seam_status_coverage_rate"] == 0.5
    assert report["policy"]["decision_owner_assignment_status"] == "ROLE_ONLY_PENDING_NAMED_ASSIGNMENT"
    missing_entry = {entry["row_id"]: entry for entry in report["entries"]}["ROW-SEAM-QFT-GR-001"]
    assert missing_entry["primary_owner"] is None
    assert missing_entry["secondary_owner"] is None
    assert missing_entry["seam_class"] == "UNSPECIFIED"
    assert missing_entry["governance_complete"] is None
    assert missing_entry["physics_complete"] is None
    assert missing_entry["seam_status_resolution"] == "MISSING_CANONICAL_SEAM_STATUS"