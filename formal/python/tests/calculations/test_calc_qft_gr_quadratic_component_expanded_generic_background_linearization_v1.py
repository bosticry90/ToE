from __future__ import annotations

from formal.python.toe.calculations import (
    calc_qft_gr_quadratic_component_expanded_generic_background_linearization_v1
    as calculation,
)
from formal.python.tools import (
    qft_gr_quadratic_component_expanded_generic_background_linearization_v1_result_review
    as review,
)
from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    canonical_json_bytes,
    read_json,
)


def test_calculation_and_review_artifacts_are_current() -> None:
    assert calculation.OUTPUT_PATH.read_bytes() == canonical_json_bytes(
        calculation.build_calculation()
    )
    assert review.OUTPUT_PATH.read_bytes() == canonical_json_bytes(
        review.build_review()
    )


def test_component_graph_is_closed_and_topologically_sorted() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    graph = artifact["component_dag"]
    assert graph["node_count"] == 3950
    assert graph["reference_closure"] == "PASS"
    assert graph["unnamed_placeholder_count"] == 0
    assert all(review._node_graph_checks(artifact).values())


def test_independent_component_inventory_is_64_in_every_chart() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    equations = artifact["component_equations"]
    assert equations["component_counts"] == {
        "g": 10,
        "R": 1,
        "r": 4,
        "c": 40,
        "S": 9,
    }
    assert equations["equation_count_per_chart"] == 64
    assert all(review._equation_inventory_checks(artifact).values())


def test_off_shell_on_shell_and_gauge_forms_remain_distinct() -> None:
    forms = read_json(calculation.OUTPUT_PATH)["forms"]
    assert forms["off_shell"]["background_residuals_retained"] == 64
    assert forms["on_shell"]["R6_applied_only_after_component_Jacobian"] is True
    assert forms["gauge_compatible"]["H_mu"] == "0"
    assert forms["gauge_compatible"]["delta_H_mu"] == "0"
    assert forms["gauge_compatible"]["constraint_additions"] == "ZERO"


def test_all_ten_trace_charts_are_present() -> None:
    charts = read_json(calculation.OUTPUT_PATH)["component_equations"][
        "tracefree_atlas_equations"
    ]
    assert len(charts) == 10
    assert {
        row["chart_id"].removeprefix("TRACEFREE_CHART_PIVOT_")
        for row in charts
    } == review.SYMMETRIC_COMPONENTS
    assert all(row["independent_component_count"] == 9 for row in charts)


def test_Minkowski_regression_is_exact() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    regression = artifact["minkowski_regression"]
    assert regression["matrix_shape"] == [128, 128]
    assert regression["nonzero_entry_count"] == 224
    assert regression["entry_positions_and_coefficients_identical"] is True
    assert review._minkowski_checks(artifact)


def test_stage_2_does_not_claim_later_results() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    claims = artifact["claim_boundary"]
    assert claims["component_background_linearization_complete"] is True
    assert claims["exact_generic_companion_spectrum_derived"] is False
    assert claims["constraint_tangent_improvement_established"] is False
    assert claims["generic_polynomial_frequency_growth_established"] is False
    assert claims["variable_coefficient_estimate_established"] is False
    assert claims["nonlinear_local_well_posedness_established"] is False
    assert artifact["selected_next_target"] == review.EXPECTED_NEXT_TARGET


def test_independent_review_accepts_only_bounded_stage_3() -> None:
    artifact = read_json(review.OUTPUT_PATH)
    assert artifact["accepted"] is True
    assert artifact["failed_checks"] == []
    assert all(artifact["checks"].values())
    assert artifact["terminal_result"] == "PASSED"
    assert artifact["selected_next_target"] == review.EXPECTED_NEXT_TARGET
    rotation = artifact["authority_rotation"]
    assert rotation["stage_3_exact_companion_operator_authorized"] is True
    assert rotation["stage_4_constraint_quotient_authorized"] is False
    assert rotation["stage_5_propagator_growth_authorized"] is False
    assert rotation["subsidiary_scientific_target_authorized"] is False
