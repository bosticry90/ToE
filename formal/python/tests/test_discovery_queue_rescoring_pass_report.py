from __future__ import annotations

from pathlib import Path

from formal.python.tools.discovery_queue_rescoring_pass_report import build_report


def test_discovery_queue_rescoring_pass_supports_activation_after_bounded_adjustment() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    declaration = (
        repo_root
        / "formal"
        / "docs"
        / "release"
        / "DISCOVERY_QUEUE_RESCORING_PASS_20260411_v0.json"
    )

    payload = build_report(declaration_path=declaration, captured_at_utc="2026-04-11T23:59:59Z")

    assert payload["schema_id"] == "DISCOVERY_QUEUE_RESCORING_PASS_REPORT_20260411_v0"
    summary = payload["summary"]
    assert summary["rank3_candidate"] == "ROW-PILLAR-GR-001"
    assert summary["rank_gap_before_rescoring"] == 1
    assert summary["rank_gap_after_rescoring"] == 3
    assert summary["rank_gap_threshold"] == 3
    assert summary["activation_now_justified"] is True
    assert summary["selected_next_route"] == "ACTIVATE_NEXT_RANKED_SEAM"
    assert summary["terminal_route"] == "ACTIVATE_NEXT_RANKED_SEAM"
    assert summary["minimum_activation_delta"]["remaining_gap_needed"] == 0

    criteria = payload["criteria"]
    assert criteria["review_selected_one_bounded_rescoring"] is True
    assert criteria["bounded_adjustment_cap_respected"] is True
    assert criteria["new_rank_gap_computed"] is True