from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_maturity_contradiction_report_generate as tool


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def test_science_maturity_contradiction_report_builds_expected_families(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(tool, "COMPLETION_MATRIX_PATH", tmp_path / "formal" / "docs" / "release" / "TOE_GLOBAL_COMPLETION_MATRIX_v0.md")
    monkeypatch.setattr(tool, "MATURITY_REGISTRY_PATH", tmp_path / "formal" / "docs" / "release" / "PILLAR_DEEP_MATURITY_REGISTRY_v0.json")
    monkeypatch.setattr(tool, "SEAM_LEDGER_PATH", tmp_path / "formal" / "output" / "reports" / "seam_resolution_sla_ledger_20260416_v0.json")
    monkeypatch.setattr(tool, "DASHBOARD_REPORT_PATH", tmp_path / "formal" / "output" / "reports" / "blocker_burn_dashboard_20260416_v0.json")
    monkeypatch.setattr(tool, "PHYSICS_PROGRESS_LEDGER_PATH", tmp_path / "formal" / "output" / "reports" / "physics_progress_ledger_v0.json")

    _write_text(
        tool.COMPLETION_MATRIX_PATH,
        "| row_id | domain | lane | current_status | blocker_class | primary_target | primary_artifact | primary_gate |\n| --- | --- | --- | --- | --- | --- | --- | --- |\n| ROW-PILLAR-QM-001 | pillar | QM | OPEN | THEOREM_GAP | a | b | c |\n| ROW-SEAM-GR-QM-001 | seam | GR_QM | OPEN | PARITY_DRIFT | a | b | c |\n| ROW-SEAM-QFT-GR-001 | seam | QFT_GR | OPEN | SEAM_INTEGRATION_GAP | a | b | c |\n",
    )
    _write_json(
        tool.MATURITY_REGISTRY_PATH,
        {
            "program_status": {"PILLAR_DEEP_MATURITY_PROGRAM_STATUS_v0": "COMPLETE_BOUNDED_v0"},
            "pillars": [{
                "pillar_id": "PILLAR-QM",
                "m4_status": "COMPLETE_BOUNDED_v0",
                "m4_live_blocker_qualifier": "LIVE_THEOREM_GAP_OPEN_v0",
            }],
        },
    )
    _write_json(
        tool.SEAM_LEDGER_PATH,
        {
            "entries": [
                {
                    "row_id": "ROW-SEAM-GR-QM-001",
                    "seam_id": "SEAM-GR-QM",
                    "blocker_class": "PARITY_DRIFT",
                    "decision_state": "HOLD_RETAINED_PARITY_RESTORE_REQUIRED",
                    "governance_complete": True,
                    "physics_complete": True,
                    "seam_status_resolution": "CANONICAL_SEAM_STATUS_PINNED",
                },
                {
                    "row_id": "ROW-SEAM-QFT-GR-001",
                    "seam_id": "SEAM-QFT-GR",
                    "lane": "QFT_GR",
                    "blocker_class": "SEAM_INTEGRATION_GAP",
                    "decision_state": "HOLD_RETAINED_PENDING_BRANCH_EXCEPTION_DECISION",
                    "governance_complete": None,
                    "physics_complete": None,
                    "seam_status_resolution": "MISSING_CANONICAL_SEAM_STATUS",
                },
            ]
        },
    )
    _write_json(
        tool.DASHBOARD_REPORT_PATH,
        {
            "blocker_scoreboard": {"movement_status": "FLAT", "exception_required": True},
            "source_freshness": {"stale_input_warning": True},
            "row_promotion_readiness": {
                "rows": [
                    {"row_id": "ROW-PILLAR-QM-001", "promotion_readiness_status": "PATHS_PINNED_PENDING_GATE_RUNTIME_AND_PARITY_EVIDENCE"}
                ]
            },
        },
    )
    _write_json(
        tool.PHYSICS_PROGRESS_LEDGER_PATH,
        {
            "actual_blocker_state_change": "NO_DELTA_DETECTED_ROUTE_TO_REWORK",
            "progress_classification": "REWORK_ROUTED",
        },
    )

    report = tool.build_science_maturity_contradiction_report(
        output_path=tmp_path / "out.json",
        captured_at_utc="2026-04-16T00:00:00Z",
    )
    assert report["contradiction_status"] == "FAIL_CLOSED_CONTRADICTIONS_PRESENT"
    assert report["summary"]["contradictions_total"] == 3
    assert report["summary"]["modeled_observations_total"] == 1
    assert report["summary"]["highest_severity"] == "HIGH"
    types = {entry["contradiction_type"] for entry in report["contradictions"]}
    assert "PILLAR_M4_COMPLETE_VS_LIVE_THEOREM_GAP" not in types
    assert "SEAM_PHYSICS_COMPLETE_VS_LIVE_HOLD_OR_PARITY" in types
    assert "LIVE_SEAM_ROW_MISSING_CANONICAL_STATUS" in types
    assert "STALE_READINESS_SIGNAL_WITH_PATHS_PINNED" in types
    observations = {entry["observation_type"] for entry in report["modeled_observations"]}
    assert "PILLAR_M4_QUALIFIED_BY_LIVE_THEOREM_GAP" in observations