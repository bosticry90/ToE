from __future__ import annotations

from formal.python.tools import dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness as design


def test_descendant_necessity_and_robustness_artifacts_are_current() -> None:
    packet, manifest, report = design.build_artifacts()
    assert design.PACKET_PATH.read_bytes() == design.canonical_json_bytes(packet)
    assert design.MANIFEST_PATH.read_bytes() == design.canonical_json_bytes(manifest)
    assert design.REPORT_PATH.read_bytes() == design.canonical_json_bytes(report)


def test_necessity_and_robustness_are_separate_tracks() -> None:
    packet, _, _ = design.build_artifacts()
    assert packet["question_tracks_separate"] is True
    tracks = {item["track_id"]: item for item in packet["comparison_tracks"]}
    assert tracks["MODEL_ROBUSTNESS"]["eligible_model_ids"] == ["FULL_ACCEPTED_DESCENDANT_AWARE_SYSTEM"]
    assert tracks["MODEL_ROBUSTNESS"]["forced_truncation_eligible_for_positive_claim"] is False
    assert tracks["DESCENDANT_NECESSITY"]["invalid_comparator_is_negative_control_only"] is True


def test_invariant_special_case_is_proof_gated_and_not_generalized() -> None:
    packet, _, _ = design.build_artifacts()
    special = next(item for item in packet["comparison_tracks"] if item["track_id"] == "INVARIANT_SPECIAL_SUBDOMAIN")
    assert special["status"] == "CONDITIONAL_ON_SEPARATE_ACCEPTED_ANALYTIC_PROOF"
    assert len(special["proof_requirements"]) == 5
    assert "NOT_GENERALIZED" in special["proof_requirements"]
    assert special["absence_of_proof_blocks_only_this_comparator"] is True


def test_exact_five_normalized_axes_and_bounded_matrix_policy_are_frozen() -> None:
    packet, _, _ = design.build_artifacts()
    assert [item["axis_id"] for item in packet["parameter_axes"]] == design.PARAMETER_AXIS_IDS
    assert all(item["dimensionless"] is True for item in packet["parameter_axes"])
    assert all(item["exact_values_frozen"] is False for item in packet["parameter_axes"])
    matrix = packet["bounded_matrix_policy"]
    assert matrix["full_cartesian_sweep_forbidden"] is True
    assert matrix["future_exact_unique_scientific_row_count_minimum"] == 12
    assert matrix["future_exact_unique_scientific_row_count_maximum"] == 14
    assert matrix["exact_matrix_must_be_frozen_before_any_new_calibration_run"] is True


def test_all_observables_and_future_freeze_requirements_are_registered() -> None:
    packet, _, _ = design.build_artifacts()
    registry = packet["observable_registry"]
    assert [item["observable_id"] for item in registry["existing_observables"]] == design.EXISTING_OBSERVABLE_IDS
    assert [item["observable_id"] for item in registry["descendant_observables"]] == design.DESCENDANT_OBSERVABLE_IDS
    assert registry["future_freeze_requirements"]["delta_O_frozen_per_registered_observable_before_execution"] is True
    assert registry["future_freeze_requirements"]["no_post_result_observable_selection"] is True


def test_controls_include_blocker_regression_and_custody_attacks() -> None:
    packet, _, report = design.build_artifacts()
    positives = packet["positive_controls"]
    negatives = packet["negative_controls"]
    assert len(positives) == 8
    assert len(negatives) == 13
    blocker = next(item for item in negatives if item["control_id"] == "N_FORCE_BOTH_DESCENDANTS_ZERO_WITH_SOURCE")
    assert blocker["permanent_regression"] is True
    assert {"N_POST_EXECUTION_FAVORABLE_POINT_SELECTION", "N_FAILED_POINTS_EXCLUDED_FROM_DOMAIN"}.issubset({item["control_id"] for item in negatives})
    assert report["design_summary"]["positive_control_count"] == 8
    assert report["design_summary"]["negative_control_count"] == 13


def test_canonical_thresholds_are_reference_only_and_pilot_is_unauthorized() -> None:
    packet, _, _ = design.build_artifacts()
    policy = packet["threshold_and_pilot_policy"]
    assert policy["canonical_thresholds_are_reference_evidence_only"] is True
    assert policy["canonical_thresholds_automatically_reused"] is False
    assert policy["new_thresholds_frozen"] is False
    assert policy["pilot_authorized"] is False
    assert "parameter_axes" in policy["pilot_may_not_change"]


def test_outcomes_are_multi_axis_and_preserve_nonpass_results() -> None:
    packet, _, _ = design.build_artifacts()
    outcomes = packet["outcome_taxonomy"]
    assert [item["outcome_id"] for item in outcomes["robustness_status_classes"]] == design.ROBUSTNESS_STATUS_CLASSES
    assert [item["outcome_id"] for item in outcomes["descendant_significance_classes"]] == design.DESCENDANT_SIGNIFICANCE_CLASSES
    assert outcomes["simple_pass_fail_forbidden"] is True
    assert outcomes["negative_inconclusive_and_blocked_outcomes_preserved"] is True


def test_mutations_and_authority_boundaries_hold() -> None:
    packet, _, report = design.build_artifacts()
    assert len(packet["mutation_controls"]) == 15
    assert all(item["passed"] for item in packet["mutation_controls"])
    assert report["mutation_controls_passed"] == 15
    boundary = packet["boundary"]
    assert boundary["scientific_design_prepared"] is True
    assert boundary["scientific_design_accepted"] is False
    assert boundary["pilot_authorized"] is False
    assert boundary["canonical_robustness_execution_authorized"] is False
    assert boundary["pillar_completion_claimed"] is False
    assert packet["completed_canonical_result_reopened"] is False


def test_prompt_is_preserved() -> None:
    assert design.sha256_path(design.REPO_ROOT / design.PROMPT_RELATIVE_PATH) == design.PROMPT_SHA256
