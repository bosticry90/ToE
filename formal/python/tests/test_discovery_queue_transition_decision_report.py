from __future__ import annotations

from pathlib import Path

from formal.python.tools.discovery_queue_transition_decision_report import build_report


def test_discovery_queue_transition_defaults_to_queue_review_when_gap_is_not_clear() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    declaration = (
        repo_root
        / "formal"
        / "docs"
        / "release"
        / "DISCOVERY_QUEUE_TRANSITION_DECISION_20260411_v0.json"
    )

    payload = build_report(declaration_path=declaration, captured_at_utc="2026-04-11T23:59:59Z")

    assert payload["schema_id"] == "DISCOVERY_QUEUE_TRANSITION_DECISION_REPORT_20260411_v0"

    summary = payload["summary"]
    assert summary["selected_route"] == "EXECUTE_BOUNDED_QUEUE_REVIEW_PASS"
    assert summary["selected_route_id"] == "EXECUTE_BOUNDED_QUEUE_REVIEW_PASS"
    assert summary["next_ranked_row_id"] == "ROW-PILLAR-GR-001"
    assert summary["next_ranked_rank"] == 3
    assert summary["rank3_over_rank4_score_gap"] == 1
    assert summary["qm_stat_internal_only_confirmed"] is True
    assert summary["qft_gr_internal_only_confirmed"] is True
    assert summary["external_discriminative_leverage_established"] is False

    criteria = payload["criteria"]
    assert criteria["activation_selected"] is False
    assert criteria["rank3_score_gap_clearly_separated"] is False