from __future__ import annotations

from formal.python.toe.calculations import (
    calc_qft_gr_quadratic_component_expanded_generic_background_linearization
    as calculation,
)
from formal.python.tools import (
    qft_gr_quadratic_component_expanded_generic_background_linearization_result_review
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


def test_metric_dependent_gauge_branch_requires_third_H_jet() -> None:
    audit = calculation.gauge_jet_order_audit()
    assert audit["derivative_orders_detected"][-1] == 3
    assert audit["minimum_metric_dependent_gauge_regularization"] == "C3"
    assert audit["accepted_regularization"] == "C2"
    assert audit["accepted_contract_sufficient"] is False
    assert "H_ggg" in audit["linearization_dependency"]


def test_field_independent_gauge_branch_is_not_silently_selected() -> None:
    audit = calculation.gauge_jet_order_audit()
    branch = audit["field_independent_H_of_x_branch"]
    assert branch["C2_is_sufficient"] is True
    assert branch["not_silently_selected"] is True


def test_generic_trace_tangent_contains_background_curvature_term() -> None:
    audit = calculation.tracefree_chart_audit()
    assert audit["minkowski_zero_curvature_reduction_s33"] == (
        "s00 - s11 - s22"
    )
    assert audit["generic_difference_from_minkowski_chart"] != "0"
    assert audit[
        "using_flat_S33_relation_on_Sbar_nonzero_background_is_valid"
    ] is False


def test_background_on_shell_chart_fails_closed() -> None:
    audit = calculation.background_jet_audit()
    assert audit["nonredundant_on_shell_coordinate_set_selected"] is False
    assert audit["background_equation_substitution_order_selected"] is False
    assert audit["terminal_outcome"] == (
        "BACKGROUND_FIELD_EQUATION_SUBSTITUTION_AMBIGUOUS"
    )


def test_minkowski_control_is_preserved_byte_identifiably() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    custody = artifact["minkowski_control_custody"]
    assert custody["matrix_shape"] == [128, 128]
    assert custody["nonzero_entry_count"] == 224
    assert len(custody["sparse_entry_sha256"]) == 64
    assert custody["frequency_growth_boundary"] == {
        "auxiliary": 0,
        "physical_TT": 1,
        "full_metric": 2,
    }
    assert custody["new_generic_specialization_regression_executed"] is False


def test_generic_component_expansion_and_spectrum_remain_unclaimed() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    claims = artifact["claim_boundary"]
    assert claims["component_expanded_rhs_derived"] is False
    assert claims["component_expanded_linearization_derived"] is False
    assert claims["component_identity_checks_passed"] is False
    assert claims["exact_generic_companion_derived"] is False
    assert claims["generic_spectrum_derived"] is False
    assert claims["generic_finite_loss_established"] is False


def test_review_accepts_only_the_corrective_contract_packet() -> None:
    artifact = read_json(review.OUTPUT_PATH)
    assert artifact["accepted"] is True
    assert artifact["failed_checks"] == []
    assert artifact["selected_next_target"] == review.EXPECTED_NEXT_TARGET
    rotation = artifact["authority_rotation"]
    assert rotation["gauge_and_jet_contract_packet_authorized"] is True
    assert rotation["component_expansion_retry_authorized"] is False
    assert rotation["generic_companion_execution_authorized"] is False
    assert rotation["generic_spectral_calculation_authorized"] is False
    assert all(review.build_review()["checks"].values())
