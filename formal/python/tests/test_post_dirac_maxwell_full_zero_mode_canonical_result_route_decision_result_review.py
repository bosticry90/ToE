from __future__ import annotations

from formal.python.tools import post_dirac_maxwell_full_zero_mode_canonical_result_route_decision_result_review as review


def test_post_result_route_decision_review_is_current() -> None:
    report = review.build_review_report()
    assert review.REVIEW_REPORT_PATH.read_bytes() == review.canonical_json_bytes(report)


def test_review_binds_the_immutable_preparation_commit() -> None:
    report = review.build_review_report()
    custody = report["preparation_custody"]
    assert custody["passed"] is True
    assert custody["commit"] == review.PREPARATION_COMMIT
    assert custody["parent"] == review.PREPARATION_PARENT


def test_review_independently_binds_all_sources_and_propositions() -> None:
    report = review.build_review_report()
    audit = report["independent_evidence_audit"]
    assert audit["source_hashes_match"] is True
    assert audit["proposition_count"] == 12
    assert audit["all_propositions_match"] is True
    assert audit["all_score_support_ids_are_known"] is True


def test_reviewer_recomputes_all_weights_scores_and_totals() -> None:
    packet = review.load_json(review.PACKET_PATH)
    scoring = review.independent_scoring(packet)
    assert scoring["criterion_weights"] == review.WEIGHT_MAP
    assert scoring["packet_score_vectors_match"] is True
    assert scoring["packet_totals_match"] is True
    assert scoring["weighted_totals"] == {
        "DESCENDANT_NECESSITY_ROBUSTNESS": 56,
        "DIMENSIONAL_ASCENT_2P1": 36,
        "FIXED_CURVED_BACKGROUND_EXTENSION": 36,
        "DYNAMIC_EINSTEIN_SCALAR": 29,
        "NEXT_UNIT_PILLAR_TARGET": 34,
    }


def test_review_accepts_descendant_robustness_at_every_threshold() -> None:
    report = review.build_review_report()
    assert report["accepted"] is True
    assert report["verdict"] == "ACCEPT_ROUTE_DECISION"
    assert report["selected_candidate_id"] == "DESCENDANT_NECESSITY_ROBUSTNESS"
    assert set(report["independent_scoring"]["selected_by_threshold"].values()) == {
        "DESCENDANT_NECESSITY_ROBUSTNESS"
    }
    assert report["passed_decision_count"] == report["decision_count"] == 18


def test_review_authorizes_only_route_specific_preparation() -> None:
    report = review.build_review_report()
    authority = report["authority_rotation"]
    assert report["selected_next_target"] == review.ACCEPTED_TARGET
    assert authority["post_result_route_decision_accepted"] is True
    assert authority["descendant_necessity_robustness_preparation_authorized"] is True
    assert authority["robustness_design_accepted"] is False
    assert authority["robustness_parameter_family_frozen"] is False
    assert authority["robustness_execution_authorized"] is False
    assert authority["canonical_result_reopened"] is False


def test_all_nonpromotion_boundaries_remain_false() -> None:
    authority = review.build_review_report()["authority_rotation"]
    assert authority["pillar_completion_authorized"] is False
    assert authority["seam_admissibility_or_closure_authorized"] is False
    assert authority["empirical_adequacy_authorized"] is False
    assert authority["C_k_dynamics_authorized"] is False
    assert authority["CCFT_validation_authorized"] is False
    assert authority["master_action_promotion_authorized"] is False


def test_prompt_is_preserved() -> None:
    assert review.PROMPT_DEPENDENCY_ROLE == "DEMOTE_TO_NONBLOCKING_PROVENANCE"
