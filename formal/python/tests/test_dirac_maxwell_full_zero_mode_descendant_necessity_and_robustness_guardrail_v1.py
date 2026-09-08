from __future__ import annotations

from formal.python.tools import dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_guardrail_v1 as guardrail


def test_guardrail_v1_artifacts_are_current() -> None:
    packet, manifest, report = guardrail.build_artifacts()
    assert guardrail.PACKET_PATH.read_bytes() == guardrail.canonical_json_bytes(packet)
    assert guardrail.MANIFEST_PATH.read_bytes() == guardrail.canonical_json_bytes(manifest)
    assert guardrail.REPORT_PATH.read_bytes() == guardrail.canonical_json_bytes(report)


def test_exact_five_axis_levels_and_positive_loading_rule_are_frozen() -> None:
    levels = guardrail.axis_level_freeze()
    assert set(levels) == {"ETA_Q", guardrail.REPLACEMENT_AXIS_ID, "THETA_W", "DELTA_THETA_PSI", "MU_MASS_DOMAIN"}
    assert all(axis["exact_values_frozen"] for axis in levels.values())
    loading = levels[guardrail.REPLACEMENT_AXIS_ID]
    assert loading["levels"]["ZERO"] == 0.0
    assert loading["levels"]["CANONICAL"] == guardrail.CANONICAL_LOADING
    assert loading["levels"]["LOW_NONZERO"] == guardrail.LOW_LOADING
    assert loading["levels"]["HIGH"] == guardrail.HIGH_LOADING
    assert loading["loading_odds_multiplier"] == 4.0
    assert loading["upper_admissibility_ceiling"] < 1.0


def test_exact_fourteen_row_matrix_is_unique_bounded_and_reconstructible() -> None:
    packet = guardrail.build_packet()
    rows = packet["scientific_matrix"]
    audit = packet["matrix_wide_reconstruction_audit"]
    assert len(rows) == 14
    assert audit["unique_requested_tuple_count"] == 14
    assert audit["canonical_anchor_count"] == 1
    assert audit["one_at_a_time_count"] == 10
    assert audit["interaction_corner_count"] == 3
    assert audit["all_positive_bases_strictly_positive"] is True
    assert audit["all_loading_values_bounded"] is True
    assert audit["all_five_axis_round_trips_pass"] is True
    assert audit["maximum_loading_round_trip_error"] <= guardrail.ROUND_TRIP_TOLERANCE


def test_row_construction_order_and_cross_axis_round_trip_are_explicit() -> None:
    for row in guardrail.build_packet()["scientific_matrix"]:
        assert len(row["construction_order"]) == 11
        assert row["construction_order"][0] == "set ETA_Q"
        assert row["construction_order"][-1] == "enforce frozen round-trip tolerance"
        assert row["round_trip_passed"] is True
        assert row["initial_data_domain_passed"] is True
        assert row["positive_base_strictly_positive"] is True
        assert row["gauge_equivalent_loading_error"] == 0.0


def test_invalid_comparator_preserves_parent_provenance_without_becoming_zero_loading() -> None:
    packet = guardrail.build_packet()
    policy = packet["comparator_policy"]
    assert policy["forced_comparator_eligible_for_positive_robustness_claim"] is False
    assert policy["recompute_as_zero_for_scientific_axis_forbidden"] is True
    for row in packet["scientific_matrix"]:
        comparator = row["comparator_provenance"]
        assert comparator["requested_parent_row_loading"] == row["requested_axis_values"][guardrail.REPLACEMENT_AXIS_ID]
        assert comparator["comparator_realized_loading"] is None
        assert comparator["comparator_realized_loading_status"] == "NOT_PHYSICALLY_ELIGIBLE"
        assert comparator["eligible_only_for_descendant_necessity_negative_control"] is True


def test_observables_materiality_thresholds_and_pilot_subset_are_frozen_without_execution() -> None:
    packet = guardrail.build_packet()
    inventory = packet["observable_freeze"]["inventory"]
    assert len(inventory["existing_observables"]) == 10
    assert len(inventory["descendant_observables"]) == 9
    assert inventory["all_observable_ids_frozen"] is True
    thresholds = packet["threshold_freeze"]
    assert thresholds["scientific_materiality_thresholds_frozen"] is True
    assert thresholds["threshold_sensitivity_values"] == [0.05, 0.1, 0.2]
    assert thresholds["numerical_acceptance_threshold_values_frozen"] is False
    pilot = packet["pilot_freeze"]
    assert pilot["pilot_row_ids"] == guardrail.PILOT_ROW_IDS
    assert pilot["pilot_subset_frozen"] is True
    assert pilot["pilot_authorized"] is False
    implementation = pilot["implementation_requirements_before_any_pilot_run"]
    assert implementation["new_versioned_pilot_implementation_required"] is True
    assert implementation["mass_must_be_an_explicit_runtime_parameter_not_a_module_global"] is True
    assert implementation["all_five_axes_must_round_trip_before_time_evolution"] is True


def test_all_twenty_normalization_regressions_pass() -> None:
    packet = guardrail.build_packet()
    controls = packet["normalization_regression_controls"]
    assert len(controls) == 20
    assert all(item["permanent_regression"] for item in controls)
    assert all(item["passed"] for item in controls)
    historical = packet["normalization_audit"]["historical_signed_axis"]
    assert historical["ratio_exceeds_one"] is True
    assert historical["sign_changes_across_crossing"] is True
    assert 0.0 < historical["zero_denominator_crossing_scale"] < 0.001
    frozen = packet["control_freeze"]
    assert frozen["all_control_ids_frozen"] is True
    assert len(frozen["accepted_positive_control_ids"]) == 8
    assert len(frozen["accepted_negative_control_ids"]) == 13
    assert len(frozen["normalization_regression_control_ids"]) == 20


def test_result_classes_remain_multi_axis_and_preserve_blocked_results() -> None:
    taxonomy = guardrail.build_packet()["result_classification_freeze"]
    assert len(taxonomy["robustness_status_classes"]) == 5
    assert len(taxonomy["descendant_significance_classes"]) == 3
    assert taxonomy["taxonomy_frozen"] is True
    assert taxonomy["multi_axis_classification_required"] is True
    assert taxonomy["negative_inconclusive_and_blocked_outcomes_preserved"] is True
    assert taxonomy["difficult_or_failed_rows_cannot_be_dropped"] is True


def test_mutations_are_independently_diagnosed() -> None:
    controls = guardrail.build_packet()["mutation_controls"]
    assert len(controls) == 18
    assert all(item["passed"] for item in controls)
    assert all(item["one_intended_premise_changed"] for item in controls)
    assert all(item["actual_diagnostics"] == [item["expected_diagnostic"]] for item in controls)


def test_authority_and_semantic_nonconfusion_boundaries_hold() -> None:
    packet = guardrail.build_packet()
    semantics = packet["semantic_role_separation"]
    assert semantics["signed_total_energy_is_physical_conservation_diagnostic"] is True
    assert semantics["positive_loading_is_design_coordinate_only"] is True
    assert semantics["conservation_equations_rewritten_with_positive_denominator"] is False
    authority = packet["authority_boundary"]
    assert authority["robustness_pilot_authorized"] is False
    assert authority["robustness_parameter_calibration_authorized"] is False
    assert authority["robustness_execution_authorized"] is False
    assert authority["canonical_E_REPRO_result_remains_accepted"] is True
    assert all(value is False for value in packet["nonclaims"].values())
    assert guardrail.PROMPT_DEPENDENCY_ROLE == "DEMOTE_TO_NONBLOCKING_PROVENANCE"
