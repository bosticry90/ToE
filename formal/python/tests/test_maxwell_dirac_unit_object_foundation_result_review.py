from __future__ import annotations

from formal.python.tools import maxwell_dirac_unit_object_foundation_result_review as review


def test_foundation_review_is_accepted_and_current() -> None:
    expected = review.build_review_report()
    actual = review.load_json(review.REVIEW_REPORT_PATH)
    assert actual == expected
    assert actual["accepted"] is True
    assert actual["verdict"] == "ACCEPT"
    assert actual["passed_decision_count"] == actual["decision_count"] == 14


def test_foundation_review_independently_closes_dimensions() -> None:
    report = review.build_review_report()
    audit = report["independent_dimension_audit"]
    assert audit["passed"] is True
    assert audit["vector_failures"] == []
    assert audit["internal_dimensions_passed"] is True
    assert all(audit["term_checks"].values())
    assert audit["dimension_order_passed"] is True


def test_foundation_review_authorizes_only_analytic_reduction() -> None:
    report = review.build_review_report()
    rotation = report["authority_rotation"]
    assert report["selected_next_target"] == review.ACCEPTED_NEXT_TARGET
    assert rotation["foundation_accepted"] is True
    assert rotation["resolution_execution_readiness"] is True
    assert rotation["analytic_reduction_preparation_authorized"] is True
    assert rotation["numerical_guardrail_authorized"] is False
    assert rotation["Maxwell_Dirac_result_claimed"] is False
    assert review.sha256_path(review.REPO_ROOT / review.PROMPT_RELATIVE_PATH) == review.PROMPT_SHA256
