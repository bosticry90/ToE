from __future__ import annotations

from formal.python.tools import pillar_seam_unit_mapping_ledger_first_unit_selector_result_review as review


def test_selector_review_is_accepted_and_current() -> None:
    expected = review.build_review_report()
    actual = review.load_json(review.REVIEW_REPORT_PATH)
    assert actual == expected
    assert actual["accepted"] is True
    assert actual["verdict"] == "ACCEPT"
    assert actual["failed_decision_ids"] == []
    assert actual["passed_decision_count"] == actual["decision_count"] == 12


def test_selector_review_recomputes_every_score_and_sensitivity() -> None:
    report = review.build_review_report()
    assert len(report["independently_recomputed_rows"]) == 7
    assert all(len(row["scores"]) == 8 for row in report["independently_recomputed_rows"])
    assert set(report["independently_recomputed_sensitivity"].values()) == {
        "PILLAR-SR-units_and_dimensions-v0"
    }
    assert report["selected_weighted_score"] == 51


def test_selector_review_authorizes_foundation_preparation_only() -> None:
    report = review.build_review_report()
    assert report["selected_next_target"] == review.ACCEPTED_NEXT_TARGET
    assert report["selected_row_resolution_execution_ready"] is False
    assert report["authority_rotation"]["foundation_preparation_authorized"] is True
    assert report["authority_rotation"]["unit_resolution_execution_authorized"] is False
    assert report["authority_rotation"]["Maxwell_Dirac_result_authorized"] is False
    assert review.PROMPT_DEPENDENCY_ROLE == "DEMOTE_TO_NONBLOCKING_PROVENANCE"
