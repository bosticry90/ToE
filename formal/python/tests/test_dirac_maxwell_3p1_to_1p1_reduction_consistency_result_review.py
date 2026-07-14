from __future__ import annotations

from formal.python.tools import dirac_maxwell_3p1_to_1p1_reduction_consistency_result_review as review


def test_independent_review_artifact_is_current() -> None:
    report = review.build_review_report()
    assert review.REVIEW_REPORT_PATH.read_bytes() == review.canonical_json_bytes(report)


def test_independent_algebra_reconstructs_clifford_and_counterexample() -> None:
    audit = review.independent_algebra_audit()
    assert audit["Clifford_passed"] is True
    assert len(audit["Clifford_residuals"]) == 10
    assert audit["longitudinal_sector_mixing_norm"] == "0.0e+00"
    assert float(audit["transverse_sector_mixing_min_norm"]) > 0
    assert audit["counterexample_norm"] == "1"
    assert audit["counterexample_sources_transverse_equation"] is True


def test_review_accepts_the_bounded_blocker_not_the_reduction() -> None:
    report = review.build_review_report()
    assert report["accepted"] is True
    assert report["verdict"] == "B-BLOCKED"
    assert report["blocker_confirmed"] is True
    assert report["passed_decision_count"] == report["decision_count"] == 14
    assert report["authority_rotation"]["reduction_accepted"] is False
    assert report["authority_rotation"]["bounded_blocker_accepted"] is True


def test_review_selects_only_a_post_block_route_decision() -> None:
    report = review.build_review_report()
    assert report["selected_next_target"] == review.POST_BLOCK_ROUTE_TARGET
    assert report["post_block_route_decision_candidates"] == [
        "repair reduction",
        "adopt a native 1+1 model",
        "move to 2+1",
        "change the matter sector",
    ]
    assert report["post_block_route_selected_automatically"] is False
    assert report["authority_rotation"]["post_block_route_decision_preparation_authorized"] is True
    assert report["authority_rotation"]["numerical_guardrail_authorized"] is False
    assert report["authority_rotation"]["execution_authorized"] is False


def test_preparation_custody_and_prompt_are_exact() -> None:
    report = review.build_review_report()
    assert report["preparation_custody"]["passed"] is True
    assert review.sha256_path(review.REPO_ROOT / review.PROMPT_RELATIVE_PATH) == review.PROMPT_SHA256
