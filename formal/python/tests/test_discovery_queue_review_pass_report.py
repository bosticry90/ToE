from __future__ import annotations

from pathlib import Path

from formal.python.tools.discovery_queue_review_pass_report import build_report


def test_discovery_queue_review_pass_reports_weak_rank3_and_bounded_rescore_route() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    declaration = (
        repo_root
        / "formal"
        / "docs"
        / "release"
        / "DISCOVERY_QUEUE_REVIEW_PASS_20260411_v0.json"
    )

    payload = build_report(declaration_path=declaration, captured_at_utc="2026-04-11T23:59:59Z")

    assert payload["schema_id"] == "DISCOVERY_QUEUE_REVIEW_PASS_REPORT_20260411_v0"
    summary = payload["summary"]
    assert summary["rank3_candidate"] == "ROW-PILLAR-GR-001"
    assert summary["rank_separation_status"] == "WEAK_OR_NOISY"
    assert summary["review_outcome"] == "QUEUE_REVIEW_SUPPORTS_ONE_BOUNDED_QUEUE_RESCORING"
    assert summary["selected_next_route"] == "EXECUTE_ONE_BOUNDED_QUEUE_RESCORING"
    assert summary["minimum_activation_delta"]["required_rank3_over_rank4_gap"] == 3
    assert summary["minimum_activation_delta"]["current_rank3_over_rank4_gap"] == 1
    assert summary["minimum_activation_delta"]["additional_gap_needed"] == 2

    criteria = payload["criteria"]
    assert criteria["transition_route_matches_expected_queue_review"] is True
    assert criteria["rank_gap_meets_threshold"] is False