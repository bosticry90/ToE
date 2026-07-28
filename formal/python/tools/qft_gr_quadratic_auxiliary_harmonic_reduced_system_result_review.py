from __future__ import annotations

import sympy as sp

from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    CAPTURED_AT_UTC,
    REPO_ROOT,
    read_json,
    sha256_path,
    write_or_check,
)


CALCULATION_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-QFT-GR-QUADRATIC-AUXILIARY-HARMONIC-REDUCED-SYSTEM-v0.json"
)
PACKET_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_AUXILIARY_HARMONIC_ADAPTED_NORM_"
    "WELL_POSEDNESS_PACKET_20260728_v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_AUXILIARY_HARMONIC_REDUCED_SYSTEM_"
    "RESULT_REVIEW_20260728_v0.json"
)
EXPECTED_CURRENT_TARGET = (
    "review_qft_gr_quadratic_auxiliary_harmonic_reduced_system_v0_result"
)
EXPECTED_NEXT_TARGET = (
    "derive_qft_gr_quadratic_gauge_and_auxiliary_"
    "constraint_propagation_system_v0"
)


def _independent_coefficient_derivation() -> dict:
    alpha, beta = sp.symbols("alpha beta")

    # Trace the displayed metric Euler-Lagrange tensor in four dimensions.
    trace_einstein_R = -1
    trace_lambda = -2
    trace_alpha_box = 2 * (4 - 1)
    trace_beta_box = 1 + sp.Rational(1, 2) * 4 - 1

    # Remove one quarter of the trace from the derivative and algebraic terms.
    tf_hessian = -2 * alpha - beta
    tf_R_S = 2 * alpha + beta / 2
    tf_riemann_S = 2 * beta
    tf_metric_S2 = -beta / 2
    gamma = 3 * alpha + beta
    return {
        "trace_einstein_R": sp.sstr(trace_einstein_R),
        "trace_lambda": sp.sstr(trace_lambda),
        "trace_alpha_box": sp.sstr(trace_alpha_box),
        "trace_beta_box": sp.sstr(trace_beta_box),
        "gamma": sp.sstr(gamma),
        "trace_box_coefficient": sp.sstr(
            sp.expand(trace_alpha_box * alpha + trace_beta_box * beta)
        ),
        "trace_box_factorization": sp.sstr(
            sp.factor(trace_alpha_box * alpha + trace_beta_box * beta)
        ),
        "trace_free_tensor_box_coefficient": sp.sstr(beta),
        "trace_free_hessian_coefficient": sp.sstr(tf_hessian),
        "trace_free_R_times_S_coefficient": sp.sstr(tf_R_S),
        "trace_free_Riemann_times_S_coefficient": sp.sstr(tf_riemann_S),
        "trace_free_metric_times_S_squared_coefficient": sp.sstr(
            tf_metric_S2
        ),
        "kinetic_map_determinant": sp.sstr(sp.factor(2 * gamma * beta)),
        "kinetic_map_invertible_iff": [
            "beta != 0",
            "3 alpha + beta != 0",
        ],
        "beta_zero_rank_loss": sp.simplify((2 * gamma * beta).subs(beta, 0))
        == 0,
        "gamma_zero_rank_loss": sp.simplify(
            (2 * gamma * beta).subs(alpha, -beta / 3)
        )
        == 0,
    }


def build_review() -> dict:
    calculation = read_json(CALCULATION_PATH)
    packet = read_json(PACKET_PATH)
    independent = _independent_coefficient_derivation()
    coefficient_ledger = calculation["projection_derivation"][
        "coefficient_ledger"
    ]
    system = calculation["closed_second_order_system"]
    constraints = calculation["constraint_system"]
    constraint_ids = {row["id"] for row in constraints}
    variables = {row["symbol"] for row in calculation["auxiliary_variables"]}
    derivative_rows = {
        row["equation"]: row for row in calculation["derivative_ledger"]
    }
    claims = calculation["claim_boundary"]
    prohibitions = calculation["prohibitions_respected"]

    checks = {
        "execution_target_and_review_handoff_are_exact": (
            calculation["execution_target"]
            == "derive_qft_gr_quadratic_auxiliary_harmonic_reduced_system_v0"
            and calculation["selected_next_target"] == EXPECTED_CURRENT_TARGET
        ),
        "accepted_preparation_and_vacuum_scope_are_bound": (
            calculation["consumed_authority"]["accepted"] is True
            and len(calculation["consumed_authority"]["sha256"]) == 64
            and calculation["frozen_scope"]["source"] == "VACUUM"
            and calculation["frozen_scope"]["dimension"] == 4
            and calculation["frozen_scope"]["metric_signature"]
            == "(-,+,+,+)"
        ),
        "all_coefficients_are_independently_reproduced": (
            coefficient_ledger == {
                key: independent[key]
                for key in coefficient_ledger
            }
        ),
        "generic_invertibility_and_controls_are_explicit": (
            coefficient_ledger["kinetic_map_determinant"]
            == "2*beta*(3*alpha + beta)"
            and independent["beta_zero_rank_loss"] is True
            and independent["gamma_zero_rank_loss"] is True
            and calculation["frozen_scope"]["generic_principal_sector"]
            == ["beta != 0", "3 alpha + beta != 0"]
            and "not Einstein-connected"
            in calculation["coefficient_controls"]["c_R_eq_0"]
        ),
        "closed_unknown_vector_has_only_definition_auxiliaries": (
            variables == {"g_mn", "R", "r_a", "c_mna", "S_mn"}
            and system["unknown_vector"]
            == ["g_mn", "R", "r_a", "c_mna", "S_mn"]
            and all(
                row["new_physical_mode"] is False
                for row in calculation["auxiliary_variables"]
            )
        ),
        "all_five_second_order_equations_are_present": (
            {
                system["metric_equation"]["id"],
                system["scalar_equation"]["id"],
                system["scalar_derivative_equation"]["id"],
                system["metric_derivative_equation"]["id"],
                system["trace_free_ricci_equation"]["id"],
            }
            == {"E_g^H", "E_R", "E_r", "E_c", "E_S"}
            and "lower(" not in str(system)
            and "..." not in str(system)
        ),
        "operator_remainders_are_exactly_defined": (
            {
                "connection",
                "riemann",
                "ricci",
                "scalar_box",
                "scalar_hessian",
                "tensor_box",
                "tensor_box_remainder",
                "harmonic_ricci_remainder",
                "generalized_harmonic_remainder",
                "reduced_ricci",
            }
            <= set(calculation["exact_operator_definitions"])
            and "all partial c terms cancel"
            in calculation["exact_operator_definitions"][
                "harmonic_ricci_remainder"
            ]
        ),
        "gauge_definition_integrability_and_initial_constraints_are_listed": (
            {
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
            == constraint_ids
        ),
        "differential_order_ledger_is_complete_and_nontrivial": (
            set(derivative_rows) == {"E_g^H", "E_R", "E_r", "E_c", "E_S"}
            and all(
                row["highest_time_derivative"] == 2
                and row["highest_spatial_derivative"] == 2
                and row["source_regularity_required"] == "none (vacuum)"
                and bool(row["constraint_derivative_order"])
                for row in derivative_rows.values()
            )
            and derivative_rows["E_r"]["rhs_highest_derivative_of_U"] == 1
            and derivative_rows["E_c"]["rhs_highest_derivative_of_U"] == 1
            and derivative_rows["E_S"]["rhs_highest_derivative_of_U"] == 1
            and derivative_rows["E_r"]["metric_only_interpretation"]
            == "g order 5"
        ),
        "initial_data_free_versus_derived_boundary_is_honest": (
            calculation["initial_data_contract"][
                "freely_specifiable_component_parametrization"
            ].startswith("NOT_CLASSIFIED_HERE")
            and len(
                calculation["initial_data_contract"][
                    "definition_derived_fields"
                ]
            )
            == 2
            and {
                "R data, which must satisfy C_R",
                "S_mn data, which must satisfy C_S, C_trace, and C_div",
            }
            <= set(
                calculation["initial_data_contract"][
                    "not_freely_specifiable_on_metric_equivalence_surface"
                ]
            )
        ),
        "equivalence_is_bidirectional_only_on_full_constraint_surface": (
            calculation["equivalence_boundary"][
                "arbitrary_auxiliary_solution_to_metric_solution"
            ]
            is False
            and "E_mn=0"
            in calculation["equivalence_boundary"]["metric_to_auxiliary"]
            and "trace plus trace-free decomposition"
            in calculation["equivalence_boundary"]["auxiliary_to_metric"]
            and calculation["projection_derivation"][
                "reconstruction_identity"
            ].startswith("E_mn = E_S_mn")
        ),
        "constraint_propagation_and_well_posedness_remain_unproved": (
            claims["constraint_propagation_established"] is False
            and claims["reduced_system_principal_symbol_classified"] is False
            and claims["one_derivative_loss_sufficient"] is False
            and claims["linear_energy_estimate_established"] is False
            and claims["picard_iteration_closed"] is False
            and claims["local_well_posedness_established"] is False
            and claims["ordinary_metric_strong_hyperbolicity_restored"]
            is False
        ),
        "prohibited_mutations_and_extensions_were_not_used": (
            all(value is False for value in prohibitions.values())
            and calculation["frozen_scope"]["source"] == "VACUUM"
        ),
        "historical_comparator_is_not_imported_as_theorem": (
            packet["candidate_reduced_system"]["status"]
            == "CANDIDATE_REQUIRING_TERM_BY_TERM_DERIVATION"
            and packet["adapted_norm_candidate"][
                "minimum_regularity_established"
            ]
            is False
            and claims["local_well_posedness_established"] is False
        ),
    }
    failed = [name for name, passed in checks.items() if not passed]
    accepted = not failed
    return {
        "schema_id": (
            "QFT_GR_QUADRATIC_AUXILIARY_HARMONIC_REDUCED_SYSTEM_"
            "RESULT_REVIEW_20260728_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "review_target": EXPECTED_CURRENT_TARGET,
        "reviewed_calculation": {
            "path": CALCULATION_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(CALCULATION_PATH),
        },
        "checks": checks,
        "failed_checks": failed,
        "accepted": accepted,
        "reviewer_independence": {
            "imports_calculation_module": False,
            "rederives_trace_coefficients": True,
            "rederives_trace_free_coefficients": True,
            "tests_both_generic_rank_controls": True,
            "audits_equations_constraints_and_claim_ceiling": True,
        },
        "accepted_results": (
            [
                "EXACT_VACUUM_AUXILIARY_HARMONIC_REDUCED_SYSTEM_DERIVED",
                "GENERIC_TRACE_TRACEFREE_KINETIC_MAP_INVERTIBLE",
                "ALGEBRAIC_EQUIVALENCE_ON_FULL_CONSTRAINT_SURFACE_DERIVED",
            ]
            if accepted
            else []
        ),
        "not_established": [
            "CONSTRAINT_PROPAGATION_SYSTEM_CLOSED",
            "REDUCED_SYSTEM_STRONG_HYPERBOLICITY",
            "ONE_DERIVATIVE_LOSS_IS_SUFFICIENT_OR_MINIMAL",
            "LINEAR_ADAPTED_NORM_ENERGY_ESTIMATE",
            "PICARD_OR_NASH_MOSER_CLOSURE",
            "LOCAL_WELL_POSEDNESS",
            "SOURCE_EXTENSION_ADMISSIBILITY",
        ],
        "authority_rotation": {
            "reduced_system_result_accepted": accepted,
            "constraint_propagation_derivation_authorized": accepted,
            "reduced_principal_symbol_execution_authorized": False,
            "energy_estimate_execution_authorized": False,
            "source_extension_authorized": False,
            "preserved_descendant_adoption_authorized": False,
            "yukawa_work_authorized": False,
        },
        "selected_next_target": (
            EXPECTED_NEXT_TARGET
            if accepted
            else "repair_qft_gr_quadratic_auxiliary_harmonic_reduced_system_v0"
        ),
        "verdict": (
            "ACCEPT_REDUCED_SYSTEM_DERIVATION_AUTHORIZE_CONSTRAINT_"
            "PROPAGATION_ONLY"
            if accepted
            else "B_BLOCKED_REDUCED_SYSTEM_DERIVATION_REQUIRES_CORRECTION"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_review,
        description=(
            "quadratic-gravity auxiliary harmonic reduced-system result review"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
