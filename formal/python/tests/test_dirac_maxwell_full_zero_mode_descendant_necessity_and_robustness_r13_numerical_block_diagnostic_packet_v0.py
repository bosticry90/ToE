from __future__ import annotations

import pytest

from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_r13_numerical_block_diagnostic_packet_v0
    as diagnostic,
)


@pytest.fixture(scope="module")
def artifacts() -> tuple[dict, dict, dict]:
    return diagnostic.build_artifacts()


@pytest.fixture(scope="module")
def packet(artifacts: tuple[dict, dict, dict]) -> dict:
    return artifacts[0]


def test_generated_diagnostic_artifacts_are_current(
    artifacts: tuple[dict, dict, dict],
) -> None:
    packet, manifest, report = artifacts
    assert diagnostic.PACKET_PATH.read_bytes() == diagnostic.canonical_json_bytes(packet)
    assert diagnostic.MANIFEST_PATH.read_bytes() == diagnostic.canonical_json_bytes(manifest)
    assert diagnostic.REPORT_PATH.read_bytes() == diagnostic.canonical_json_bytes(report)


def test_bound_sources_and_all_203_outputs_have_exact_custody(packet: dict) -> None:
    custody = packet["source_custody"]
    assert custody["passed"] is True
    assert custody["all_source_artifact_hashes_exact"] is True
    assert custody["source_artifact_hashes"] == diagnostic.EXPECTED_SOURCE_HASHES
    assert custody["canonical_run_outputs_checked"] == 203
    assert custody["canonical_run_output_hash_failures"] == []
    assert custody["review_verdict_exact"] is True
    assert custody["review_selected_this_target"] is True


def test_preparation_is_read_only_and_does_not_import_the_simulator(packet: dict) -> None:
    before = diagnostic.canonical_root_digest()
    diagnostic.build_artifacts()
    after = diagnostic.canonical_root_digest()
    source = diagnostic.sha256_path(diagnostic.REPO_ROOT / diagnostic.GENERATOR_RELATIVE_PATH)
    source_text = (diagnostic.REPO_ROOT / diagnostic.GENERATOR_RELATIVE_PATH).read_text(
        encoding="utf-8"
    )
    assert before == after == packet["source_custody"]["canonical_output_root_digest"]
    assert source
    assert "dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_v2 as simulator" not in source_text
    assert packet["diagnostic_scope"]["new_simulation_run_count"] == 0
    assert packet["diagnostic_scope"]["canonical_output_mutation_count"] == 0


def test_four_exact_timelines_reconstruct_crossings_and_final_monotone_maxima(
    packet: dict,
) -> None:
    timelines = packet["failure_timelines"]
    assert timelines["sample_count"] == 17
    assert len(timelines["timelines"]) == 4
    assert timelines["all_initial_values_pass"] is True
    assert timelines["all_maxima_at_final_time"] is True
    assert timelines["all_absolute_magnitudes_monotone_nondecreasing"] is True
    assert [row["time"] for row in timelines["threshold_crossing_order"]] == pytest.approx(
        [0.0125, 0.03125, 0.04375]
    )
    assert timelines["threshold_crossing_order"][0]["threshold_ids"] == [
        "maximum_continuity_residual",
        "maximum_longitudinal_Maxwell_residual",
    ]
    assert all(
        len(row["residual_over_frozen_ceiling"])
        == len(row["residual_over_own_maximum"])
        == 17
        for row in timelines["timelines"]
    )


def test_maximum_ceiling_ratios_match_the_accepted_four_failures(packet: dict) -> None:
    by_id = {
        row["threshold_id"]: row["maximum_ceiling_ratio"]
        for row in packet["failure_timelines"]["timelines"]
    }
    assert by_id["maximum_Gauss_residual"] == pytest.approx(1.137287508309052)
    assert by_id["maximum_continuity_residual"] == pytest.approx(1.2479160771145665)
    assert by_id["maximum_exchange_longitudinal_residual"] == pytest.approx(
        4.280402909147904
    )
    assert by_id["maximum_longitudinal_Maxwell_residual"] == pytest.approx(
        1.3873886375989492
    )


def test_all_four_residuals_have_clustered_descriptive_tolerance_response(
    packet: dict,
) -> None:
    response = packet["tolerance_response"]
    assert response["all_four_residual_maxima_strictly_decrease_with_tighter_tolerance"]
    assert response["overall_exponent_minimum"] == pytest.approx(0.7448900948221593)
    assert response["overall_exponent_maximum"] == pytest.approx(0.7559176564888908)
    assert response["overall_exponent_median"] == pytest.approx(0.7486818198236936)
    assert all(
        0.7 < row["overall_1eM08_to_1eM12_exponent"] < 0.8
        for row in response["residual_tolerance_response"]
    )
    assert "descriptive" in response["interpretation"]


def test_solver_histories_show_no_late_iteration_or_scalar_residual_growth(
    packet: dict,
) -> None:
    rows = {
        row["solver_tolerance"]: row for row in packet["tolerance_response"]["solver_runs"]
    }
    assert rows[1e-8]["maximum_iterations"] == 3
    assert rows[1e-10]["maximum_iterations"] == 4
    assert rows[1e-12]["maximum_iterations"] == 5
    assert all(row["late_iteration_increase"] == 0 for row in rows.values())
    assert all(row["iterations_constant_after_initial_state"] for row in rows.values())
    assert all(row["solver_residual_nonincreasing_after_first_step"] for row in rows.values())
    assert all(row["all_steps_converged"] for row in rows.values())


def test_all_eleven_axis_sharing_neighbors_pass_without_causal_overreach(packet: dict) -> None:
    contrast = packet["R13_neighbor_contrast"]
    assert contrast["axis_sharing_neighbor_count"] == 11
    assert contrast["all_axis_sharing_neighbors_pass"] is True
    assert all(row["all_four_pass"] for row in contrast["axis_sharing_neighbors"])
    assert contrast["individual_axis_setting_sufficient_in_tested_matrix"] is False
    assert all(
        row["all_matching_rows_pass"] for row in contrast["per_axis_descriptive_check"]
    )
    assert "cannot identify" in contrast["interaction_inference_boundary"]


def test_exact_cancellation_kappa_is_withheld_and_proxy_is_explicitly_bounded(
    packet: dict,
) -> None:
    conditioning = packet["cancellation_conditioning"]
    exact = conditioning["requested_exact_sector_transfer_kappa"]
    proxy = conditioning["available_field_energy_vs_registered_exchange_proxy"]
    assert exact["status"] == "NOT_DERIVABLE_FROM_PRESERVED_OUTPUTS"
    assert exact["missing_fields"] == sorted(diagnostic.EXACT_CANCELLATION_REQUIRED_FIELDS)
    assert proxy["status"] == "DESCRIPTIVE_PROXY_NOT_EXACT_REQUESTED_KAPPA"
    assert proxy["final_unregularized_proxy"] == pytest.approx(1874510.136260484)
    assert proxy["final_floor_regularized_proxy"] == pytest.approx(1002.5923769167093)
    assert "cannot establish" in proxy["interpretation_boundary"]


def test_unregistered_component_diagnostics_remain_unresolved(packet: dict) -> None:
    availability = {item["diagnostic_id"]: item for item in packet["data_availability"]}
    assert availability["DISCRETE_MAXWELL_TO_CONTINUITY_IDENTITY_CLOSURE"]["status"] == (
        "NOT_DERIVABLE_FROM_PRESERVED_OUTPUTS"
    )
    assert availability["SOLVER_EQUATION_BLOCK_DOMINANCE"]["status"] == (
        "NOT_DERIVABLE_FROM_PRESERVED_OUTPUTS"
    )
    assert availability["HIGHER_PRECISION_ARITHMETIC_CONTRIBUTION"]["status"] == (
        "NOT_TESTABLE_WITH_EXISTING_DOUBLE_PRECISION_OUTPUTS_ONLY"
    )
    assert packet["discrete_identity_closure"]["new_law_proposed"] is False
    assert packet["iteration_and_nonlinear_residual_history"][
        "equation_block_history_status"
    ] == "NOT_REGISTERED"


def test_failed_thresholds_are_absolute_ceilings_not_small_denominator_ratios(
    packet: dict,
) -> None:
    audit = packet["precision_and_scale_audit"]
    assert audit["all_four_are_absolute_ceilings_without_row_denominators"] is True
    assert audit["small_denominator_threshold_explanation_supported"] is False
    assert audit["cancellation_inside_the_registered_exchange_calculation_remains_possible"]
    assert all(
        row["threshold_class"] == "ABSOLUTE_NUMERICAL_CEILING"
        and row["contains_ratio_denominator"] is False
        for row in audit["failed_threshold_semantics"]
    )


def test_packet_is_prepared_only_and_rotates_to_independent_review(packet: dict) -> None:
    assert packet["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
    assert packet["selected_next_target"] == diagnostic.SELECTED_NEXT_TARGET
    assert packet["passed_decision_count"] == packet["decision_count"] == 16
    assert packet["failed_decision_ids"] == []
    boundary = packet["authority_boundary"]
    assert boundary["packet_prepared"] is True
    assert boundary["packet_independently_accepted"] is False
    assert boundary["new_simulation_authorized"] is False
    assert boundary["rerun_authorized"] is False
    assert boundary["threshold_change_authorized"] is False
    assert boundary["materiality_assigned"] is False
    assert boundary["conditional_or_broad_robustness_authorized"] is False
    assert boundary["new_E_REPRO_authorized"] is False
