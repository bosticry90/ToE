from __future__ import annotations

from formal.python.tools import dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_result_review as review


def test_robustness_design_review_artifact_is_current() -> None:
    report = review.build_review_report()
    assert review.REVIEW_REPORT_PATH.read_bytes() == review.canonical_json_bytes(report)


def test_review_binds_immutable_preparation_commit() -> None:
    custody = review.build_review_report()["preparation_custody"]
    assert custody["passed"] is True
    assert custody["commit"] == review.PREPARATION_COMMIT
    assert custody["parent"] == review.PREPARATION_PARENT


def test_review_reconstructs_all_sources_and_propositions() -> None:
    audit = review.build_review_report()["independent_evidence_audit"]
    assert audit["source_count"] == 6
    assert audit["proposition_count"] == 13
    assert audit["all_sources_and_propositions_match"] is True


def test_review_reconstructs_tracks_axes_and_bounded_matrix() -> None:
    audit = review.build_review_report()["independent_design_audit"]
    assert audit["question_tracks_separate"] is True
    assert audit["full_only_positive_robustness"] is True
    assert audit["forced_truncation_negative_only"] is True
    assert audit["special_subdomain_proof_gated"] is True
    assert audit["all_axes_match"] is True
    assert audit["matrix_bounded"] is True


def test_review_reconstructs_observables_controls_and_blocker_regression() -> None:
    audit = review.build_review_report()["independent_design_audit"]
    assert audit["existing_observables_match"] is True
    assert audit["descendant_observables_match"] is True
    assert audit["descendant_definitions_match"] is True
    assert audit["future_observable_freezes_required"] is True
    assert audit["positive_controls_match"] is True
    assert audit["negative_controls_match"] is True
    assert audit["blocker_is_permanent_regression"] is True


def test_review_preserves_threshold_and_pilot_boundaries() -> None:
    audit = review.build_review_report()["independent_design_audit"]
    assert audit["canonical_thresholds_reference_only"] is True
    assert audit["pilot_unauthorized"] is True
    assert audit["scientific_design_immutable_during_future_pilot"] is True


def test_review_accepts_multi_axis_outcomes_and_all_decisions() -> None:
    report = review.build_review_report()
    audit = report["independent_design_audit"]
    assert audit["robustness_outcomes_match"] is True
    assert audit["descendant_outcomes_match"] is True
    assert audit["multi_axis_nonpass_preservation"] is True
    assert report["accepted"] is True
    assert report["verdict"] == "ACCEPT_SCIENTIFIC_DESIGN"
    assert report["passed_decision_count"] == report["decision_count"] == 25


def test_review_authorizes_only_robustness_guardrail_preparation() -> None:
    report = review.build_review_report()
    authority = report["authority_rotation"]
    assert report["selected_next_target"] == review.ACCEPTED_TARGET
    assert authority["scientific_design_accepted"] is True
    assert authority["robustness_guardrail_preparation_authorized"] is True
    assert authority["robustness_guardrail_accepted"] is False
    assert authority["pilot_authorized"] is False
    assert authority["exact_parameter_matrix_frozen"] is False
    assert authority["thresholds_frozen"] is False
    assert authority["canonical_robustness_execution_authorized"] is False
    assert authority["canonical_result_reopened"] is False


def test_nonpromotion_and_prompt_boundaries_hold() -> None:
    report = review.build_review_report()
    authority = report["authority_rotation"]
    assert authority["universal_robustness_authorized"] is False
    assert authority["physical_necessity_in_nature_authorized"] is False
    assert authority["pillar_completion_authorized"] is False
    assert authority["seam_closure_authorized"] is False
    assert authority["C_k_dynamics_authorized"] is False
    assert authority["master_action_validation_authorized"] is False
    assert review.PROMPT_DEPENDENCY_ROLE == "DEMOTE_TO_NONBLOCKING_PROVENANCE"
