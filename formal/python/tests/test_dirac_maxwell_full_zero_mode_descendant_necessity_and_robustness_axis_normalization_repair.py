from __future__ import annotations

from formal.python.tools import dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_axis_normalization_repair as repair


def test_axis_normalization_repair_artifacts_are_current() -> None:
    packet, manifest, report = repair.build_artifacts()
    assert repair.PACKET_PATH.read_bytes() == repair.canonical_json_bytes(packet)
    assert repair.MANIFEST_PATH.read_bytes() == repair.canonical_json_bytes(manifest)
    assert repair.REPORT_PATH.read_bytes() == repair.canonical_json_bytes(report)


def test_signed_component_audit_explains_counterexample_and_singularity() -> None:
    audit = repair.component_and_singularity_audit()
    counterexample = audit["positive_pi_over_two_counterexample"]
    assert counterexample["historical_signed_ratio"] > 1.0
    assert counterexample["signed_remainder_over_total"] < 0.0
    assert counterexample["signed_remainder_over_descendant"] < 0.0
    assert counterexample["exact_negative_contributor_identified"] == "gamma2_interaction"
    singularity = audit["signed_denominator_singularity_probe"]
    assert 0.0 < singularity["positive_zero_crossing_scale"] < 0.001
    assert singularity["historical_ratio_is_singular_at_crossing"] is True


def test_closed_candidates_are_scored_without_using_recommendation() -> None:
    packet = repair.build_packet()
    assert packet["candidate_order"] == repair.CANDIDATE_ORDER
    assert len(packet["scored_candidates"]) == 5
    assert all(len(item["criterion_scores"]) == 8 for item in packet["scored_candidates"])
    assert all(item["weighted_total"] == sum(row["weighted_score"] for row in item["criterion_scores"]) for item in packet["scored_candidates"])
    assert packet["user_recommendation"]["used_as_score_input"] is False


def test_rest_number_positive_reference_wins_stably() -> None:
    packet = repair.build_packet()
    assert packet["canonical_selection"]["selected_candidate_id"] == repair.SELECTED_CANDIDATE_ID
    assert packet["canonical_selection"]["selected_weighted_total"] == 62
    assert packet["selection_stable_at_all_sensitivity_thresholds"] is True
    assert all(item["selected_candidate_id"] == repair.SELECTED_CANDIDATE_ID for item in packet["sensitivity_analysis"])
    signed = next(item for item in packet["scored_candidates"] if item["candidate_id"] == "SIGNED_TOTAL_RATIO_DIAGNOSTIC_ONLY")
    assert signed["minimum_gates_passed"] is False


def test_historical_and_replacement_axes_are_versioned_and_semantically_distinct() -> None:
    contract = repair.selected_axis_contract()
    historical = contract["historical_axis"]
    replacement = contract["replacement_axis"]
    assert historical["axis_id"] == repair.HISTORICAL_AXIS_ID
    assert historical["status"] == "REJECTED_AS_BOUNDED_AXIS_RETAINED_AS_SIGNED_DIAGNOSTIC"
    assert replacement["axis_id"] == repair.REPLACEMENT_AXIS_ID
    assert replacement["domain"] == "0 <= f_perp_positive_initial < 1"
    assert replacement["gauge_invariant"] is True
    assert replacement["signed_conserved_energy_remains_separate"] is True
    assert replacement["forbidden_interpretation"] == "Fraction of the conserved signed physical energy stored in descendants."


def test_selected_coordinate_is_bounded_gauge_invariant_monotone_and_invertible() -> None:
    audit = repair.selected_candidate_audit()
    assert audit["phase_independent"] is True
    assert audit["gauge_transform_audit"]["invariant"] is True
    assert audit["strictly_monotone_for_positive_amplitudes"] is True
    assert audit["zero_maps_exactly_to_zero"] is True
    assert audit["large_finite_loading_below_one"] is True
    assert audit["inverse_reconstruction_maximum_error"] <= 1e-15
    assert audit["holonomy_does_not_break_boundedness"] is True
    assert audit["signed_total_energy_mutated_by_coordinate_definition"] is False


def test_canonical_initial_condition_maps_reproducibly() -> None:
    mapping = repair.selected_candidate_audit()["canonical_mapping"]
    assert mapping["historical_value"] < 1.0
    assert 0.0 < mapping["replacement_value"] < 1.0
    assert abs(mapping["replacement_value"] - 0.2131315883288088) <= 1e-15
    assert mapping["positive_base_energy"] > mapping["descendant_energy"]


def test_shortcuts_values_pilot_and_execution_remain_forbidden() -> None:
    packet = repair.build_packet()
    shortcuts = packet["shortcut_policy"]
    assert shortcuts["clamping_allowed"] is False
    assert shortcuts["tolerance_based_domain_repair_allowed"] is False
    assert shortcuts["absolute_value_substitution_allowed"] is False
    replacement = packet["axis_contract"]["replacement_axis"]
    assert replacement["exact_low_anchor_high_values_frozen"] is False
    authority = packet["authority_boundary"]
    assert authority["guardrail_v1_preparation_authorized_before_review"] is False
    assert authority["robustness_pilot_authorized"] is False
    assert authority["robustness_execution_authorized"] is False
    assert authority["canonical_result_reopened"] is False


def test_mutations_are_independently_diagnosed() -> None:
    controls = repair.build_packet()["mutation_controls"]
    assert len(controls) == 15
    assert all(item["passed"] for item in controls)
    assert all(item["actual_diagnostics"] == [item["expected_diagnostic"]] for item in controls)


def test_nonclaims_and_prompt_are_preserved() -> None:
    authority = repair.build_packet()["authority_boundary"]
    assert authority["accepted_reduction_reopened"] is False
    assert authority["action_or_stress_tensor_changed"] is False
    assert authority["pillar_completion_claimed"] is False
    assert authority["seam_closure_claimed"] is False
    assert authority["C_k_dynamics_claimed"] is False
    assert authority["CCFT_validation_claimed"] is False
    assert authority["master_action_promotion_claimed"] is False
    assert repair.sha256_path(repair.REPO_ROOT / repair.PROMPT_RELATIVE_PATH) == repair.PROMPT_SHA256
