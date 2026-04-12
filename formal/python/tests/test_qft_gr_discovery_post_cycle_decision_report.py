from __future__ import annotations

from pathlib import Path

from formal.python.tools.qft_gr_discovery_post_cycle_decision_report import build_report


def test_qft_gr_post_cycle_decision_defaults_to_keep_internal_probe_blocked() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    declaration = (
        repo_root
        / "formal"
        / "docs"
        / "release"
        / "QFT_GR_DISCOVERY_POST_CYCLE_DECISION_20260411_v0.json"
    )

    payload = build_report(declaration_path=declaration, captured_at_utc="2026-04-11T23:59:59Z")

    assert payload["schema_id"] == "QFT_GR_DISCOVERY_POST_CYCLE_DECISION_REPORT_20260411_v0"
    summary = payload["summary"]
    assert summary["interpretation"] == "INTERNAL_DISCRIMINATIVE_ONLY"
    assert summary["post_cycle_decision"] == "KEEP_QFT_GR_AS_INTERNAL_DISCRIMINATOR_LANE"
    assert summary["decision_disposition"] == "KEEP_INTERNAL_LANE"
    assert summary["probe_lane_allowed"] is False
    assert summary["next_action"] == "HOLD_QFT_GR_INTERNAL_AND_BLOCK_PROBE_EXPANSION"
