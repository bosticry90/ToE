from __future__ import annotations

from formal.python.tools import dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_guardrail_result_review as review


def test_review_artifact_is_current() -> None:
    expected = review.canonical_json_bytes(review.build_review())
    assert review.REVIEW_REPORT_PATH.read_bytes() == expected


def test_reviewer_reproduces_counterexample_without_preparation_logic() -> None:
    counterexample = review.independent_phase_counterexample()
    assert counterexample["delta_theta_psi_radians"] > 0.0
    assert counterexample["f_perp_initial"] > 1.0
    assert counterexample["exceeds_declared_upper_bound"] is True
    assert counterexample["calculation_imports_preparation_generator"] is False


def test_all_review_decisions_are_independently_reconstructed() -> None:
    artifact = review.build_review()
    assert len(artifact["review_decisions"]) == 16
    assert all(artifact["review_decisions"].values())
    assert artifact["preparation_generator_imported"] is False
    assert artifact["blocker_confirmed"] is True
    assert artifact["verdict"] == review.BLOCKER_CODE


def test_authority_rotates_only_to_axis_normalization_repair() -> None:
    artifact = review.build_review()
    authority = artifact["authority_rotation"]
    assert artifact["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert authority["axis_normalization_repair_preparation_authorized"] is True
    assert authority["robustness_guardrail_accepted"] is False
    assert authority["exact_parameter_matrix_frozen"] is False
    assert authority["robustness_pilot_authorized"] is False
    assert authority["canonical_robustness_execution_authorized"] is False
    assert authority["repair_method_selected"] is False


def test_prior_result_and_nonclaims_are_preserved() -> None:
    authority = review.build_review()["authority_rotation"]
    assert authority["canonical_E_REPRO_result_remains_accepted"] is True
    assert authority["accepted_scientific_design_rewritten"] is False
    assert authority["pillar_completion_authorized"] is False
    assert authority["seam_closure_authorized"] is False
    assert authority["C_k_dynamics_authorized"] is False
    assert authority["CCFT_validation_authorized"] is False
    assert authority["master_action_promotion_authorized"] is False


def test_preparation_commit_and_prompt_are_immutable() -> None:
    binding = review.bind_preparation()
    assert binding["preparation_commit"] == review.PREPARATION_COMMIT
    assert binding["preparation_parent"] == review.PREPARATION_PARENT
    assert review.sha256_path(review.REPO_ROOT / review.PROMPT_RELATIVE_PATH) == review.PROMPT_SHA256
