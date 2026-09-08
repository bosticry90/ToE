from __future__ import annotations

from formal.python.toe.calculations import (
    calc_qft_gr_quadratic_generic_background_linearization_gauge_and_jet_contract
    as calculation,
)
from formal.python.tools import (
    qft_gr_quadratic_generic_background_linearization_gauge_and_jet_contract_result_review
    as review,
)
from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    canonical_json_bytes,
)


def test_calculation_and_independent_review_are_current() -> None:
    assert calculation.OUTPUT_PATH.read_bytes() == canonical_json_bytes(
        calculation.build_calculation()
    )
    assert review.OUTPUT_PATH.read_bytes() == canonical_json_bytes(
        review.build_review()
    )


def test_strict_harmonic_branch_has_no_gauge_source_jets() -> None:
    contract = calculation.build_calculation()["strict_harmonic_gauge_contract"]
    assert contract["H_mu"] == "0"
    assert contract["delta_H_mu"] == "0"
    assert contract["gauge_source_jet_orders_zero"] == [0, 1, 2, 3]
    assert contract["constraint_additions"] == "ZERO"


def test_tracefree_atlas_covers_all_ten_pivots() -> None:
    atlas = calculation.build_calculation()["tracefree_atlas"]
    charts = atlas["charts"]
    assert len(charts) == 10
    assert {row["pivot_component"] for row in charts} == set(
        calculation.SYMMETRIC_COMPONENTS
    )
    assert all(len(row["independent_components"]) == 9 for row in charts)


def test_metric_equivalence_regularity_is_not_reduced_C3() -> None:
    regularity = calculation.build_calculation()["regularity_contract"]
    assert regularity["combined_sufficient_metric_class"] == "C6"
    assert regularity["combined_sufficient_metric_perturbation_class"] == "C6"
    assert regularity["optimality_claimed"] is False


def test_rewrite_contract_terminates_and_has_unique_normal_forms() -> None:
    rewrite = calculation.build_calculation()["rewrite_contract"]
    assert rewrite["termination_established"] is True
    assert rewrite["critical_pairs_closed"] is True
    assert rewrite["normal_form_unique"] is True
    assert rewrite["normalization_idempotent"] is True


def test_stage_1_does_not_claim_stage_2_or_later_results() -> None:
    result = calculation.build_calculation()
    claims = result["claim_boundary"]
    assert claims["component_expanded_linearization_derived"] is False
    assert claims["exact_generic_companion_operator_derived"] is False
    assert claims["constraint_tangent_projector_constructed"] is False
    assert claims["generic_finite_loss_established"] is False
    reviewed = review.build_review()
    assert reviewed["accepted"] is True
    assert reviewed["terminal_result"] == "PASSED"
    assert all(reviewed["checks"].values())
