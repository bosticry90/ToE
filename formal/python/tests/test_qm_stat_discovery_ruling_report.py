from __future__ import annotations

from pathlib import Path

from formal.python.tools.qm_stat_discovery_ruling_report import build_report


def test_qm_stat_discovery_ruling_report_enforces_single_terminal_outcome() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    declaration = (
        repo_root
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_DISCOVERY_RULING_20260411_v0.json"
    )

    payload = build_report(declaration_path=declaration, captured_at_utc="2026-04-11T23:36:00Z")

    assert payload["schema_id"] == "QM_STAT_DISCOVERY_RULING_REPORT_20260411_v0"
    summary = payload["summary"]
    assert summary["single_terminal_outcome_enforced"] is True
    assert summary["ruling_status"] == "TERMINAL_OUTCOME_CONFIRMED"
    assert summary["ruling"] == "DISCRIMINATOR_PRODUCED"
    assert summary["terminal_outcome"] == "DISCRIMINATOR_PRODUCED"
    assert summary["terminal_outcome_allowed"] is True
