from __future__ import annotations

from formal.python.tools import dirac_maxwell_full_zero_mode_discrete_numerical_guardrail_result_review as review


def test_numerical_guardrail_review_artifact_is_current() -> None:
    report = review.build_review_report()
    assert review.REVIEW_REPORT_PATH.read_bytes() == review.canonical_json_bytes(report)


def test_independent_link_covariance_and_Wilson_audit_reproduce() -> None:
    audit = review.independent_discrete_audit()
    assert audit["both_species_covariant"] is True
    assert audit["group_update_norm_identity"] == "|exp(i Delta_theta) U|=|U|=1"
    assert audit["descendants_gauge_invariant_under_zero_modes"] is True
    assert audit["doubler_mass_shift_at_pi_over_a"] == "2/a"
    assert len(audit["Wilson_dispersion_samples_r1"]) == 3


def test_review_accepts_all_guardrail_decisions() -> None:
    report = review.build_review_report()
    assert report["accepted"] is True
    assert report["verdict"] == "ACCEPT"
    assert report["passed_decision_count"] == report["decision_count"] == 20
    assert report["authority_rotation"]["numerical_guardrail_accepted"] is True
    assert report["authority_rotation"]["pure_1p1_truncation_rehabilitated"] is False


def test_review_authorizes_only_non_authoritative_pilot() -> None:
    report = review.build_review_report()
    authority = report["authority_rotation"]
    assert report["selected_next_target"] == review.ACCEPTED_TARGET
    assert authority["non_authoritative_pilot_execution_authorized"] is True
    assert authority["pilot_result_authoritative"] is False
    assert authority["canonical_execution_authorized"] is False
    assert authority["canonical_result_claimed"] is False


def test_preparation_custody_and_prompt_are_exact() -> None:
    report = review.build_review_report()
    assert report["preparation_custody"]["passed"] is True
    assert review.PROMPT_DEPENDENCY_ROLE == "DEMOTE_TO_NONBLOCKING_PROVENANCE"
