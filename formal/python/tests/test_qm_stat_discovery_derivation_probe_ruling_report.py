from __future__ import annotations

from pathlib import Path

from formal.python.tools.qm_stat_discovery_derivation_probe_ruling_report import build_report


def test_qm_stat_discovery_derivation_probe_ruling_report_emits_allowed_outcome() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    declaration = (
        repo_root
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_DISCOVERY_DERIVATION_PROBE_RULING_20260411_v0.json"
    )

    payload = build_report(declaration_path=declaration, captured_at_utc="2026-04-11T23:59:20Z")

    assert payload["schema_id"] == "QM_STAT_DISCOVERY_DERIVATION_PROBE_RULING_REPORT_20260411_v0"
    summary = payload["summary"]
    assert summary["derivation_outcome"] == "DISCRIMINATOR_PRODUCED"
    assert summary["probe_signal"] == "PROBE_NONDISCRIMINATIVE"
    assert summary["path_falsification_observed"] is False
    assert summary["paired_outcome"] == "DERIVATION_INTERNAL_ONLY_PROBE_NONDISCRIMINATIVE"
    assert summary["paired_outcome"] in summary["allowed_outcomes"]
