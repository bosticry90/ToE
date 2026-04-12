from __future__ import annotations

from pathlib import Path

from formal.python.tools.qm_stat_discovery_numerical_probe_report import build_report


def test_qm_stat_discovery_numerical_probe_report_is_bounded_and_aligned() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    declaration = (
        repo_root
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_DISCOVERY_NUMERICAL_PROBE_20260411_v0.json"
    )

    payload = build_report(declaration_path=declaration, captured_at_utc="2026-04-11T23:56:00Z")

    assert payload["schema_id"] == "QM_STAT_DISCOVERY_NUMERICAL_PROBE_REPORT_20260411_v0"
    summary = payload["summary"]
    assert summary["target_row"] == "ROW-SEAM-QM-STAT-001"
    assert summary["top_rank_row"] == "ROW-SEAM-QM-STAT-001"
    assert summary["seam_alignment"] is True
    assert summary["ruling"] == "DISCRIMINATOR_PRODUCED"
    assert summary["max_probe_cycles"] == 1
    assert summary["probe_lane_status"] == "BOUNDED_PROBE_LANE_READY"
    assert summary["probe_runnable"] is True
