from __future__ import annotations

import sympy as sp

from formal.python.toe.calculations import (
    calc_qft_gr_quadratic_exact_generic_frozen_companion_operator
    as calculation,
)
from formal.python.tools import (
    qft_gr_quadratic_exact_generic_frozen_companion_operator_result_review
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


def test_exact_minkowski_companion_shape_and_top_identity() -> None:
    matrix = calculation.minkowski_control_companion()
    assert matrix.shape == (128, 128)
    for row in range(64):
        assert matrix[row, 64 + row] == 1
        assert sum(
            matrix[row, column] != 0 for column in range(128)
        ) == 1


def test_exact_minkowski_metric_scalar_and_derivative_blocks() -> None:
    matrix = calculation.minkowski_control_companion()
    k1, k2, k3 = sp.symbols("k1 k2 k3", real=True)
    m_r = sp.Symbol("m_R", real=True)
    rho_squared = k1**2 + k2**2 + k3**2
    assert matrix[64, 50] == -sp.Rational(1, 2)
    assert matrix[68, 50] == sp.Rational(1, 2)
    assert matrix[64, 55] == 2
    assert matrix[114, 50] == -rho_squared - m_r
    assert matrix[115, 114] == -m_r
    assert matrix[116, 50] == -sp.I * k1 * m_r
    assert matrix[74, 114] == -sp.Rational(1, 2)
    assert matrix[74, 119] == 2


def test_exact_minkowski_spin2_block() -> None:
    matrix = calculation.minkowski_control_companion()
    k1, k2, k3 = sp.symbols("k1 k2 k3", real=True)
    m_r = sp.Symbol("m_R", real=True)
    m_s = sp.Symbol("m_S", real=True)
    a = sp.Symbol("a", real=True)
    rho_squared = k1**2 + k2**2 + k3**2
    assert matrix[119, 50] == -a * m_r / 4
    assert matrix[119, 115] == -a
    assert matrix[119, 55] == -rho_squared + m_s
    assert matrix[126, 50] == a * m_r / 4
    assert matrix[126, 53] == -sp.I * a * k2


def test_minkowski_sparse_ledger_is_complete_and_placeholder_free() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    control = artifact["exact_minkowski_control"]
    entries = control["sparse_entries"]
    assert control["matrix_shape"] == [128, 128]
    assert control["nonzero_entry_count"] == 224
    assert len(
        {(row["row"], row["column"]) for row in entries}
    ) == 224
    assert all(
        token not in row["value"]
        for row in entries
        for token in ("O(", "lower", "remainder", "Q^H", "L^S")
    )


def test_generic_operator_fails_closed_on_exact_missing_inputs() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    audit = artifact["generic_operator_closure_audit"]
    claims = artifact["claim_boundary"]
    assert audit["answer"] is False
    assert audit["terminal_outcome"] == (
        "GENERIC_BACKGROUND_OPERATOR_NOT_YET_CLOSED"
    )
    assert set(audit["blocking_placeholders_found_in_predecessor"]) == {
        "Q^H_mn",
        "Q_mn(g,c)",
        "L^S_mn",
        "partial_a F^R",
        "partial_a F^g_mn",
    }
    assert claims["exact_generic_background_operator_derived"] is False
    assert claims["generic_characteristic_asymptotics_derived"] is False
    assert claims["generic_finite_loss_established"] is False
    assert claims["generic_fractional_root_splitting_excluded"] is False


def test_review_accepts_control_and_authorizes_component_expansion_only() -> None:
    artifact = read_json(review.OUTPUT_PATH)
    assert artifact["accepted"] is True
    assert artifact["failed_checks"] == []
    assert artifact["selected_next_target"] == review.EXPECTED_NEXT_TARGET
    assert artifact["accepted_results"] == [
        (
            "MINKOWSKI_FROZEN_COMPANION_OPERATOR_EXACTLY_"
            "DERIVED_CONTROL_ONLY"
        ),
        "GENERIC_BACKGROUND_OPERATOR_NOT_YET_CLOSED",
        (
            "GENERIC_SUBPRINCIPAL_SPECTRAL_CLASSIFICATION_"
            "NOT_AUTHORIZED"
        ),
        "CONSTRAINT_TANGENT_PROJECTOR_REMAINS_BLOCKED",
        "NO_VARIABLE_OR_NONLINEAR_ESTIMATE",
    ]
    rotation = artifact["authority_rotation"]
    assert rotation[
        "component_expanded_background_linearization_authorized"
    ] is True
    assert rotation["generic_spectral_calculation_authorized"] is False
    assert rotation["constraint_tangent_projection_authorized"] is False
    assert rotation["variable_coefficient_estimate_authorized"] is False
    assert all(review.build_review()["checks"].values())
