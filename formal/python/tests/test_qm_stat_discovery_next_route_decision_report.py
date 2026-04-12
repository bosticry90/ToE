from __future__ import annotations

from pathlib import Path

from formal.python.tools.qm_stat_discovery_next_route_decision_report import build_report


def test_qm_stat_next_route_defaults_to_next_ranked_seam_activation() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    declaration = repo_root / "formal" / "docs" / "release" / "QM_STAT_DISCOVERY_NEXT_ROUTE_DECISION_20260411_v0.json"

    payload = build_report(declaration_path=declaration, captured_at_utc="2026-04-11T23:59:56Z")

    assert payload["schema_id"] == "QM_STAT_DISCOVERY_NEXT_ROUTE_DECISION_REPORT_20260411_v0"
    summary = payload["summary"]
    assert summary["selected_route"] == "ACTIVATE_NEXT_RANKED_SEAM"
    assert summary["selected_route_id"] == "ACTIVATE_NEXT_RANKED_SEAM"
    assert summary["current_seam_row_id"] == "ROW-SEAM-QM-STAT-001"
    assert summary["next_ranked_row_id"] == "ROW-SEAM-QFT-GR-001"
    assert summary["next_action"] == "ADVANCE_DISCOVERY_QUEUE_TO_NEXT_SEAM"
    assert summary["auto_same_shape_qm_stat_rerun_allowed"] is False