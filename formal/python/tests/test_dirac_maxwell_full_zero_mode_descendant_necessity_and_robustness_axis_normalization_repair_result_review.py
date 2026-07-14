from __future__ import annotations

from formal.python.tools import dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_axis_normalization_repair_result_review as review


def test_axis_normalization_review_artifact_is_current() -> None:
    assert review.REVIEW_REPORT_PATH.read_bytes() == review.canonical_json_bytes(review.build_review())


def test_candidate_scores_and_selection_are_independently_reconstructed() -> None:
    artifact = review.build_review()
    assert artifact["candidate_weighted_totals"] == {
        "SIGNED_TOTAL_RATIO_DIAGNOSTIC_ONLY": 29,
        "ABSOLUTE_COMPONENT_BUDGET_FRACTION": 37,
        "GAUGE_COVARIANT_SPECTRAL_REFERENCE_LOADING": 50,
        "REST_NUMBER_POSITIVE_REFERENCE_LOADING": 62,
        "FIXED_PROFILE_AMPLITUDE_LOADING": 51,
    }
    assert artifact["selected_candidate_id"] == review.SELECTED_CANDIDATE_ID
    assert all(review.independently_select(threshold) == review.SELECTED_CANDIDATE_ID for threshold in (40, 42, 44, 46, 48))
    assert artifact["preparation_generator_imported"] is False


def test_scientific_properties_are_reproduced_independently() -> None:
    audit = review.independent_scientific_audit()
    assert audit["historical_counterexample_reproduced"] is True
    assert audit["historical_positive_pi_over_two_ratio"] > 1.0
    assert abs(audit["canonical_replacement_coordinate"] - 0.2131315883288088) <= 1e-15
    assert audit["canonical_positive_base"] > 0.0
    assert audit["phase_stable"] is True
    assert audit["gauge_audit"]["invariant"] is True
    assert audit["inverse_maximum_error"] <= 1e-15


def test_every_review_decision_passes() -> None:
    artifact = review.build_review()
    assert len(artifact["review_decisions"]) == 18
    assert all(artifact["review_decisions"].values())
    assert artifact["accepted"] is True
    assert artifact["verdict"] == review.VERDICT


def test_authority_rotates_only_to_guardrail_v1_preparation() -> None:
    artifact = review.build_review()
    authority = artifact["authority_rotation"]
    assert artifact["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert authority["axis_normalization_repair_accepted"] is True
    assert authority["guardrail_v1_preparation_authorized"] is True
    assert authority["historical_guardrail_v0_rewritten"] is False
    assert authority["historical_signed_axis_rehabilitated"] is False
    assert authority["exact_parameter_values_frozen"] is False
    assert authority["robustness_pilot_authorized"] is False
    assert authority["robustness_execution_authorized"] is False


def test_canonical_result_model_and_nonclaims_are_preserved() -> None:
    authority = review.build_review()["authority_rotation"]
    assert authority["canonical_E_REPRO_result_remains_accepted"] is True
    assert authority["accepted_reduction_reopened"] is False
    assert authority["action_or_stress_tensor_changed"] is False
    assert authority["pillar_completion_authorized"] is False
    assert authority["seam_closure_authorized"] is False
    assert authority["C_k_dynamics_authorized"] is False
    assert authority["CCFT_validation_authorized"] is False
    assert authority["master_action_promotion_authorized"] is False


def test_preparation_and_prompt_are_immutable() -> None:
    binding = review.bind_preparation()
    assert binding["preparation_commit"] == review.PREPARATION_COMMIT
    assert binding["preparation_parent"] == review.PREPARATION_PARENT
    assert review.sha256_path(review.REPO_ROOT / review.PROMPT_RELATIVE_PATH) == review.PROMPT_SHA256
