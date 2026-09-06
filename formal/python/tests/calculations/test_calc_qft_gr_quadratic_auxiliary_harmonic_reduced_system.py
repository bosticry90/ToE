from __future__ import annotations

from formal.python.toe.calculations import (
    calc_qft_gr_quadratic_auxiliary_harmonic_reduced_system as calculation,
)
from formal.python.tools import (
    qft_gr_quadratic_auxiliary_harmonic_reduced_system_result_review as review,
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


def test_trace_and_trace_free_coefficients_are_exact() -> None:
    coefficients = calculation.derive_projection_coefficients()
    assert coefficients == {
        "gamma": "3*alpha + beta",
        "trace_box_coefficient": "6*alpha + 2*beta",
        "trace_box_factorization": "2*(3*alpha + beta)",
        "trace_free_tensor_box_coefficient": "beta",
        "trace_free_hessian_coefficient": "-2*alpha - beta",
        "trace_free_R_times_S_coefficient": "2*alpha + beta/2",
        "trace_free_Riemann_times_S_coefficient": "2*beta",
        "trace_free_metric_times_S_squared_coefficient": "-beta/2",
        "kinetic_map_determinant": "2*beta*(3*alpha + beta)",
        "kinetic_map_invertible_iff": [
            "beta != 0",
            "3 alpha + beta != 0",
        ],
    }


def test_reduced_system_is_closed_without_an_implicit_lower_placeholder() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    system = artifact["closed_second_order_system"]
    assert system["unknown_vector"] == [
        "g_mn",
        "R",
        "r_a",
        "c_mna",
        "S_mn",
    ]
    assert {
        system["metric_equation"]["id"],
        system["scalar_equation"]["id"],
        system["scalar_derivative_equation"]["id"],
        system["metric_derivative_equation"]["id"],
        system["trace_free_ricci_equation"]["id"],
    } == {"E_g^H", "E_R", "E_r", "E_c", "E_S"}
    assert "lower(" not in str(system)
    assert "..." not in str(system)
    assert "R_mrns[g,c]" in system["trace_free_ricci_equation"][
        "coordinate_form"
    ]
    assert "L^S_mn" in system["trace_free_ricci_equation"][
        "coordinate_form"
    ]


def test_derivative_variables_are_definitions_not_new_physical_modes() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    variables = {row["symbol"]: row for row in artifact["auxiliary_variables"]}
    assert variables["r_a"]["definition"] == "partial_a R"
    assert variables["c_mna"]["definition"] == (
        "partial_a g_mn, symmetric in mn"
    )
    assert all(row["new_physical_mode"] is False for row in variables.values())
    assert artifact["prohibitions_respected"]["regularizer_added"] is False
    assert artifact["prohibitions_respected"]["fiducial_mode_added"] is False


def test_complete_constraint_classes_are_separate() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    constraints = {row["id"]: row for row in artifact["constraint_system"]}
    assert set(constraints) == {
        "C_H^a",
        "C_r_a",
        "C_c_mna",
        "C_R",
        "C_S_mn",
        "C_trace",
        "C_div_n",
        "C_curl_r_ab",
        "C_curl_c_mnab",
        "C_Hamiltonian",
        "C_momentum_a",
    }
    assert constraints["C_H^a"]["class"] == "generalized-harmonic gauge"
    assert constraints["C_Hamiltonian"]["class"] == (
        "normal-normal original metric projection"
    )
    assert constraints["C_S_mn"]["class"] == "trace-free Ricci definition"


def test_derivative_ledger_exposes_metric_regularities() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    rows = {row["equation"]: row for row in artifact["derivative_ledger"]}
    assert set(rows) == {"E_g^H", "E_R", "E_r", "E_c", "E_S"}
    assert all(row["highest_time_derivative"] == 2 for row in rows.values())
    assert all(row["highest_spatial_derivative"] == 2 for row in rows.values())
    assert rows["E_r"]["metric_only_interpretation"] == "g order 5"
    assert rows["E_c"]["metric_only_interpretation"] == "g order 3"
    assert rows["E_S"]["rhs_highest_derivative_of_U"] == 1
    assert all(
        row["source_regularity_required"] == "none (vacuum)"
        for row in rows.values()
    )
    assert all(row["constraint_derivative_order"] for row in rows.values())


def test_initial_data_are_not_mislabeled_as_freely_specifiable() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    data = artifact["initial_data_contract"]
    assert data["freely_specifiable_component_parametrization"].startswith(
        "NOT_CLASSIFIED_HERE"
    )
    assert data["definition_derived_fields"] == [
        "r_a and its normal derivative from C_r and E_R",
        "c_mna and its normal derivative from C_c and E_g^H",
    ]
    assert "R data, which must satisfy C_R" in data[
        "not_freely_specifiable_on_metric_equivalence_surface"
    ]


def test_equivalence_requires_the_full_constraint_surface() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    boundary = artifact["equivalence_boundary"]
    assert boundary["arbitrary_auxiliary_solution_to_metric_solution"] is False
    assert boundary["constraint_propagation_established_here"] is False
    assert "E_mn=0" in boundary["metric_to_auxiliary"]
    assert "trace plus trace-free decomposition" in boundary[
        "auxiliary_to_metric"
    ]


def test_review_accepts_only_constraint_propagation_as_successor() -> None:
    artifact = read_json(review.OUTPUT_PATH)
    assert artifact["accepted"] is True
    assert artifact["failed_checks"] == []
    assert artifact["selected_next_target"] == review.EXPECTED_NEXT_TARGET
    assert artifact["authority_rotation"][
        "constraint_propagation_derivation_authorized"
    ] is True
    assert artifact["authority_rotation"][
        "reduced_principal_symbol_execution_authorized"
    ] is False
    assert artifact["authority_rotation"][
        "energy_estimate_execution_authorized"
    ] is False
    assert "LOCAL_WELL_POSEDNESS" in artifact["not_established"]
    assert all(review.build_review()["checks"].values())
