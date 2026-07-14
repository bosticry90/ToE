from __future__ import annotations

from formal.python.tools import post_dirac_maxwell_reduction_blocked_route_decision_result_review as review


def test_route_decision_review_artifact_is_current() -> None:
    report = review.build_review_report()
    assert review.REVIEW_REPORT_PATH.read_bytes() == review.canonical_json_bytes(report)


def test_reviewer_recomputes_named_weights_scores_and_totals() -> None:
    packet = review.load_json(review.PACKET_PATH)
    scoring = review.independent_scoring(packet)
    assert scoring["criterion_weights"] == review.WEIGHT_MAP
    assert scoring["packet_score_vectors_match"] is True
    assert scoring["packet_totals_match"] is True
    assert scoring["weighted_totals"] == {
        "REPAIR_REDUCTION": 51,
        "ADOPT_NATIVE_1P1": 37,
        "MOVE_TO_2P1": 38,
        "CHANGE_MATTER_SECTOR": 31,
    }


def test_review_accepts_repair_at_every_sensitivity_threshold() -> None:
    report = review.build_review_report()
    assert report["accepted"] is True
    assert report["verdict"] == "ACCEPT"
    assert report["selected_candidate_id"] == "REPAIR_REDUCTION"
    assert set(report["independent_scoring"]["selected_by_threshold"].values()) == {"REPAIR_REDUCTION"}
    assert report["passed_decision_count"] == report["decision_count"] == 14


def test_review_authorizes_only_full_zero_mode_analytic_repair() -> None:
    report = review.build_review_report()
    authority = report["authority_rotation"]
    assert report["selected_next_target"] == review.ACCEPTED_TARGET
    assert authority["route_decision_accepted"] is True
    assert authority["full_zero_mode_repair_preparation_authorized"] is True
    assert authority["numerical_guardrail_authorized"] is False
    assert authority["execution_authorized"] is False
    assert authority["pure_1p1_truncation_rehabilitated"] is False


def test_review_custody_and_prompt_are_exact() -> None:
    report = review.build_review_report()
    assert report["preparation_custody"]["passed"] is True
    assert review.sha256_path(review.REPO_ROOT / review.PROMPT_RELATIVE_PATH) == review.PROMPT_SHA256
