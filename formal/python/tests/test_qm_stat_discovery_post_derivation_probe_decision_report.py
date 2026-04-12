from __future__ import annotations

from pathlib import Path

from formal.python.tools.qm_stat_discovery_post_derivation_probe_decision_report import build_report


def test_qm_stat_post_derivation_probe_decision_defaults_to_keep_internal_no_rerun() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    declaration = (
        repo_root
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_DISCOVERY_POST_DERIVATION_PROBE_DECISION_20260411_v0.json"
    )

    payload = build_report(declaration_path=declaration, captured_at_utc="2026-04-11T23:59:50Z")

    assert payload["schema_id"] == "QM_STAT_DISCOVERY_POST_DERIVATION_PROBE_DECISION_REPORT_20260411_v0"
    summary = payload["summary"]
    assert summary["paired_outcome"] == "DERIVATION_INTERNAL_ONLY_PROBE_NONDISCRIMINATIVE"
    assert summary["post_cycle_decision"] == "KEEP_QM_STAT_AS_INTERNAL_DISCRIMINATOR_LANE"
    assert summary["decision_disposition"] == "KEEP_INTERNAL_LANE"
    assert summary["auto_rerun_allowed"] is False
    assert summary["next_action"] == "HOLD_QM_STAT_INTERNAL_AND_BLOCK_AUTO_RERUN"
