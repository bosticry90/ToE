from __future__ import annotations

from pathlib import Path

from formal.python.tools.qm_stat_discovery_numerical_probe_execution_report import build_report


def test_qm_stat_discovery_numerical_probe_execution_report_is_bounded() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    declaration = (
        repo_root
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_DISCOVERY_NUMERICAL_PROBE_EXECUTION_20260411_v0.json"
    )

    payload = build_report(declaration_path=declaration, captured_at_utc="2026-04-11T23:59:10Z")

    assert payload["schema_id"] == "QM_STAT_DISCOVERY_NUMERICAL_PROBE_EXECUTION_REPORT_20260411_v0"
    summary = payload["summary"]
    assert summary["target_row"] == "ROW-SEAM-QM-STAT-001"
    assert summary["seam_alignment"] is True
    assert summary["probe_executed"] is True
    assert summary["probe_execution_status"] == "BOUNDED_PROBE_EXECUTED"
    assert summary["probe_signal"] == "PROBE_NONDISCRIMINATIVE"
    assert summary["path_falsification_observed"] is False
