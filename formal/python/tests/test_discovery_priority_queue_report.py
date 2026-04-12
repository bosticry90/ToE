from __future__ import annotations

from pathlib import Path

from formal.python.tools.discovery_priority_queue_report import build_report


def test_build_report_ranks_qm_stat_first() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    declaration = repo_root / "formal" / "docs" / "release" / "DISCOVERY_PRIORITY_QUEUE_20260411_v0.json"
    trend = repo_root / "formal" / "output" / "reports" / "governance_blocker_trend_window_20260410_v0.json"
    closure_map = repo_root / "formal" / "output" / "reports" / "governance_blocker_closure_map_20260410_v0.json"
    ledger = repo_root / "formal" / "output" / "reports" / "physics_progress_ledger_v0.json"

    payload = build_report(
        declaration_path=declaration,
        trend_path=trend,
        closure_map_path=closure_map,
        ledger_path=ledger,
        captured_at_utc="2026-04-11T22:00:00Z",
    )

    assert payload["schema_id"] == "DISCOVERY_PRIORITY_QUEUE_REPORT_20260411_v0"
    assert payload["summary"]["queue_size"] == 5
    assert payload["summary"]["top_rank_row"] == "ROW-SEAM-QM-STAT-001"
    assert payload["ranked_candidates"][0]["rank"] == 1
    assert payload["ranked_candidates"][0]["row_id"] == "ROW-SEAM-QM-STAT-001"
    assert payload["ranked_candidates"][0]["score"] >= payload["ranked_candidates"][1]["score"]
    assert payload["blocker_context"]["net_delta"] == 0
