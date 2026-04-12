from __future__ import annotations

from pathlib import Path

from formal.python.tools.qft_gr_discovery_interpretation_report import build_report


def test_qft_gr_discovery_interpretation_report_is_shadow_conservative() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    declaration = (
        repo_root
        / "formal"
        / "docs"
        / "release"
        / "QFT_GR_DISCOVERY_INTERPRETATION_20260411_v0.json"
    )

    payload = build_report(declaration_path=declaration, captured_at_utc="2026-04-11T23:59:59Z")

    assert payload["schema_id"] == "QFT_GR_DISCOVERY_INTERPRETATION_REPORT_20260411_v0"
    summary = payload["summary"]
    assert summary["target_row"] == "ROW-SEAM-QFT-GR-001"
    assert summary["ruling"] == "DISCRIMINATOR_PRODUCED"
    assert summary["execution_classification"] == "DISCOVERY_TRANCHE_EXECUTABLE"
    assert summary["interpretation"] == "INTERNAL_DISCRIMINATIVE_ONLY"
    assert summary["externally_comparable_candidate"] is False
    assert summary["probe_ready"] is False
    assert summary["path_falsified"] is False
    assert summary["probe_lane_allowed"] is False
