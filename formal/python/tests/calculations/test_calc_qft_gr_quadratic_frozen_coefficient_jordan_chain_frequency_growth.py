from __future__ import annotations

import sympy as sp

from formal.python.toe.calculations import (
    calc_qft_gr_quadratic_frozen_coefficient_jordan_chain_frequency_growth
    as calculation,
)
from formal.python.tools import (
    qft_gr_quadratic_frozen_coefficient_jordan_chain_frequency_growth_result_review
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


def test_exact_companion_has_requested_root_jordan_lengths() -> None:
    rho = sp.Integer(2)
    for length in (1, 2, 3):
        companion = calculation.second_order_wave_companion(length, rho)
        assert companion.shape == (2 * length, 2 * length)
        assert sp.factor(companion.charpoly().as_expr()) == (
            sp.Symbol("lambda") ** 2 + rho**2
        ) ** length
        for root in (-1, 1):
            shifted = (
                companion
                - sp.I * root * rho * sp.eye(2 * length)
            )
            assert 2 * length - shifted.rank() == 1
            assert 2 * length - (shifted**length).rank() == length


def test_all_fifty_chains_cover_each_root_component_once() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    roots = artifact["exact_companion"]["all_chain_mapping"]["roots"]
    for rows in roots.values():
        assert len(rows) == 50
        covered = sorted(
            component
            for row in rows
            for component in range(
                row["root_component_range"][0],
                row["root_component_range"][1] + 1,
            )
        )
        assert covered == list(range(64))
        assert sum(row["chain_length"] == 3 for row in rows) == 4
        assert sum(row["chain_length"] == 2 for row in rows) == 6
        assert sum(row["chain_length"] == 1 for row in rows) == 40


def test_exact_modal_exponentials_give_zero_one_two_losses() -> None:
    rho, time = sp.symbols("rho time", positive=True, real=True)
    for length, expected in ((1, 0), (2, 1), (3, 2)):
        metric = calculation.root_modal_generator(
            length,
            1,
            rho,
            edge_power=1,
        )
        adapted = calculation.root_modal_generator(
            length,
            1,
            rho,
            edge_power=0,
        )
        metric_exponential = sp.exp(time * metric)
        adapted_exponential = sp.exp(time * adapted)
        assert sp.Poly(
            sp.expand(
                metric_exponential[0, length - 1]
                / sp.exp(sp.I * rho * time)
            ),
            rho,
        ).degree() == expected
        assert sp.Poly(
            sp.expand(
                adapted_exponential[0, length - 1]
                / sp.exp(sp.I * rho * time)
            ),
            rho,
        ).degree() == 0


def test_block_order_graph_screen_has_no_positive_return_cycle() -> None:
    edges = calculation.metric_weighted_order_edges()
    assert len(edges) == 20
    cycles = calculation.simple_cycle_exponents(edges)
    assert cycles
    assert max(
        row["generator_frequency_exponent_sum"] for row in cycles
    ) == 0
    assert any(
        row["cycle"] in {"c->S->c", "S->c->S"}
        and row["generator_frequency_exponent_sum"] == 0
        for row in cycles
    )


def test_sector_results_keep_constraint_minimum_blocked() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    sectors = artifact["sector_results"]
    assert sectors["equal_order_auxiliary"]["minimum_frozen_loss"] == 0
    assert sectors["adapted_auxiliary"]["minimum_frozen_loss"] == 0
    assert sectors["unrestricted_metric_equivalence"][
        "pure_principal_minimum_loss_when_2alpha_plus_beta_nonzero"
    ] == 2
    assert sectors["unrestricted_metric_equivalence"][
        "pure_principal_minimum_loss_on_2alpha_plus_beta_zero_control"
    ] == 1
    assert sectors["unrestricted_metric_equivalence"][
        "complete_generic_frozen_minimum_loss"
    ] == "BLOCKED"
    assert sectors["physical_TT"]["pure_principal_minimum_loss"] == 1
    assert sectors["physical_TT"][
        "complete_generic_frozen_minimum_loss"
    ] == "BLOCKED"
    assert sectors["constraint_compatible"]["minimum_frozen_loss"] == (
        "BLOCKED"
    )
    assert sectors["constraint_compatible"]["proved_bounds"] == [1, 2]
    assert artifact["frequency_growth"][
        "complete_generic_frozen_operator"
    ]["constructed"] is False


def test_equivalence_shift_is_not_composed_with_propagator_loss() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    losses = artifact["separate_loss_maps"]
    assert losses["known_equivalence_map_shift"] == 1
    assert losses["r_prop"] == {
        "auxiliary": 0,
        "constraint_compatible": "BLOCKED_BETWEEN_1_AND_2",
        "physical_TT": (
            "PURE_PRINCIPAL_1_COMPLETE_GENERIC_FROZEN_BLOCKED"
        ),
        "unrestricted_metric_equivalence": (
            "PURE_PRINCIPAL_2_COMPLETE_GENERIC_FROZEN_BLOCKED"
        ),
    }
    assert losses["total_metric_loss_summed"] is False


def test_review_accepts_pure_principal_result_and_next_exact_operator() -> None:
    artifact = read_json(review.OUTPUT_PATH)
    assert artifact["accepted"] is True
    assert artifact["failed_checks"] == []
    assert artifact["selected_next_target"] == review.EXPECTED_NEXT_TARGET
    assert artifact["accepted_results"] == [
        "FROZEN_AUXILIARY_ZERO_LOSS_CONFIRMED",
        "PURE_PRINCIPAL_METRIC_EQUIVALENCE_TWO_DERIVATIVE_GROWTH",
        "PURE_PRINCIPAL_PHYSICAL_TT_ONE_DERIVATIVE_GROWTH",
        (
            "COMPLETE_GENERIC_FROZEN_METRIC_LOSS_BLOCKED_BY_"
            "MISSING_SUBPRINCIPAL_MATRIX"
        ),
        (
            "CONSTRAINT_RESTRICTED_LOSS_BLOCKED_BY_MISSING_"
            "TANGENT_PROJECTOR"
        ),
        "BLOCK_ORDER_GRAPH_SCREEN_HAS_NO_POSITIVE_RETURN_CYCLE",
    ]
    rotation = artifact["authority_rotation"]
    assert rotation[
        "exact_generic_frozen_companion_operator_authorized"
    ] is True
    assert rotation["constraint_tangent_projection_authorized"] is False
    assert rotation["variable_coefficient_estimate_authorized"] is False
    assert rotation["quasilinear_estimate_authorized"] is False
    assert rotation["local_existence_theorem_authorized"] is False
    assert all(review.build_review()["checks"].values())
