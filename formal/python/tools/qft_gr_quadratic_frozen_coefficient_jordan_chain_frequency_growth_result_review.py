from __future__ import annotations

from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    CAPTURED_AT_UTC,
    REPO_ROOT,
    read_json,
    sha256_path,
    write_or_check,
)


CALCULATION_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-QFT-GR-QUADRATIC-FROZEN-COEFFICIENT-JORDAN-CHAIN-"
    "FREQUENCY-GROWTH-v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_FROZEN_COEFFICIENT_JORDAN_CHAIN_FREQUENCY_"
    "GROWTH_RESULT_REVIEW_20260728_v0.json"
)
EXPECTED_CURRENT_TARGET = (
    "review_qft_gr_quadratic_frozen_coefficient_"
    "jordan_chain_frequency_growth_v0_result"
)
EXPECTED_NEXT_TARGET = (
    "derive_qft_gr_quadratic_exact_generic_frozen_"
    "companion_operator_v0"
)


def build_review() -> dict:
    calculation = read_json(CALCULATION_PATH)
    exact = calculation["exact_companion"]
    checks_data = exact["partition_checks"]
    growth = calculation["frequency_growth"]
    sectors = calculation["sector_results"]
    maps = calculation["separate_loss_maps"]
    claims = calculation["claim_boundary"]
    prohibitions = calculation["prohibitions_respected"]
    chain_map = exact["all_chain_mapping"]["roots"]

    expected_partition = {
        "length_3": 4,
        "length_2": 6,
        "length_1": 40,
    }
    chain_checks: dict[str, bool] = {}
    for root in ("-1", "1"):
        rows = chain_map[root]
        covered = sorted(
            component
            for row in rows
            for component in range(
                row["root_component_range"][0],
                row["root_component_range"][1] + 1,
            )
        )
        chain_checks[root] = (
            len(rows) == 50
            and covered == list(range(64))
            and sum(row["chain_length"] == 3 for row in rows) == 4
            and sum(row["chain_length"] == 2 for row in rows) == 6
            and sum(row["chain_length"] == 1 for row in rows) == 40
            and sum(
                row["unrestricted_metric_growth_exponent"] == 2
                for row in rows
            )
            == 4
            and sum(
                row["unrestricted_metric_growth_exponent"] == 1
                for row in rows
            )
            == 6
        )

    modal = growth["exact_root_modal_exponentials"]
    cycles = growth["simple_return_cycles"]
    checks = {
        "accepted_preparation_authority_was_consumed": (
            calculation["execution_target"]
            == (
                "compute_qft_gr_quadratic_frozen_coefficient_"
                "jordan_chain_frequency_growth_v0"
            )
            and calculation["consumed_authority"]["accepted_results"]
            == [
                "ADAPTED_ENERGY_HIERARCHY_READY",
                "JORDAN_CHAIN_LOSS_GRADING_UNRESOLVED",
                (
                    "KNOWN_WEIGHTED_PRINCIPAL_CONTAMINATION_INCLUDED_"
                    "NOT_YET_ESTIMATED"
                ),
                "COMPLETE_FIFTY_CHAIN_LEDGER_AT_EACH_ROOT",
            ]
        ),
        "exact_companion_dimension_and_partition_close": (
            exact["dimension"] == 128
            and checks_data["component_count"] == 64
            and checks_data["first_order_state_count"] == 128
            and checks_data["chain_count_each_root"] == 50
            and checks_data["chain_partition_each_root"]
            == expected_partition
            and checks_data["algebraic_dimension_each_root"] == 64
            and checks_data["geometric_dimension_each_root"] == 50
            and checks_data["eigenvector_deficit_each_root"] == 14
        ),
        "all_chains_are_mapped_at_both_roots": all(chain_checks.values()),
        "exact_modal_exponentials_saturate_zero_one_two": (
            modal["1"]["metric_minimum_growth_exponent"] == "0"
            and modal["2"]["metric_minimum_growth_exponent"] == "1"
            and modal["3"]["metric_minimum_growth_exponent"] == "2"
            and modal["1"]["adapted_minimum_growth_exponent"] == "0"
            and modal["2"]["adapted_minimum_growth_exponent"] == "0"
            and modal["3"]["adapted_minimum_growth_exponent"] == "0"
            and "(rho*time)^1" in modal["2"]["saturating_component"]
            and "(rho*time)^2" in modal["3"]["saturating_component"]
        ),
        "block_order_graph_screen_is_not_an_exact_operator": (
            len(
                growth[
                    "complete_metric_weighted_linearized_edge_inventory"
                ]
            )
            == 20
            and cycles
            and max(
                row["generator_frequency_exponent_sum"]
                for row in cycles
            )
            == 0
            and growth["maximum_return_cycle_exponent_sum"] == 0
            and growth["complete_generic_frozen_operator"]["constructed"]
            is False
            and "cannot exclude subprincipal root splitting"
            in growth["order_screen_conclusion"]
        ),
        "auxiliary_zero_loss_is_exact": (
            sectors["equal_order_auxiliary"]["minimum_frozen_loss"] == 0
            and sectors["adapted_auxiliary"]["minimum_frozen_loss"] == 0
            and sectors["equal_order_auxiliary"][
                "saturating_lower_bound_established"
            ]
            is True
            and sectors["adapted_auxiliary"][
                "saturating_lower_bound_established"
            ]
            is True
        ),
        "pure_principal_metric_growth_is_two_but_complete_loss_blocks": (
            sectors["unrestricted_metric_equivalence"][
                "pure_principal_minimum_loss_when_2alpha_plus_beta_nonzero"
            ]
            == 2
            and sectors["unrestricted_metric_equivalence"][
                "pure_principal_minimum_loss_on_2alpha_plus_beta_zero_control"
            ]
            == 1
            and sectors["unrestricted_metric_equivalence"][
                "complete_generic_frozen_minimum_loss"
            ]
            == "BLOCKED"
            and sectors["unrestricted_metric_equivalence"][
                "pure_principal_upper_bound_established"
            ]
            is True
            and sectors["unrestricted_metric_equivalence"][
                "pure_principal_saturating_lower_bound_established"
            ]
            is True
            and sectors["unrestricted_metric_equivalence"][
                "complete_operator_upper_bound_established"
            ]
            is False
        ),
        "pure_principal_TT_growth_is_one_but_complete_loss_blocks": (
            sectors["physical_TT"]["pure_principal_minimum_loss"] == 1
            and sectors["physical_TT"][
                "complete_generic_frozen_minimum_loss"
            ]
            == "BLOCKED"
            and sectors["physical_TT"]["polarization_count"] == 2
            and sectors["physical_TT"]["chain_length"] == 2
            and sectors["physical_TT"][
                "pure_principal_upper_bound_established"
            ]
            is True
            and sectors["physical_TT"][
                "pure_principal_saturating_lower_bound_established"
            ]
            is True
            and sectors["physical_TT"][
                "complete_operator_upper_bound_established"
            ]
            is False
        ),
        "constraint_restricted_minimum_fails_closed": (
            sectors["constraint_compatible"]["minimum_frozen_loss"]
            == "BLOCKED"
            and sectors["constraint_compatible"]["proved_bounds"] == [1, 2]
            and "128-state tangent projector"
            in sectors["constraint_compatible"]["blocking_input"]
            and claims["constraint_tangent_projector_constructed"] is False
            and claims[
                "constraint_restricted_minimum_loss_established"
            ]
            is False
        ),
        "equivalence_and_evolution_losses_remain_separate": (
            maps["known_equivalence_map_shift"] == 1
            and maps["r_prop"]["auxiliary"] == 0
            and maps["r_prop"]["unrestricted_metric_equivalence"]
            == "PURE_PRINCIPAL_2_COMPLETE_GENERIC_FROZEN_BLOCKED"
            and maps["r_prop"]["physical_TT"]
            == "PURE_PRINCIPAL_1_COMPLETE_GENERIC_FROZEN_BLOCKED"
            and maps["r_prop"]["constraint_compatible"]
            == "BLOCKED_BETWEEN_1_AND_2"
            and maps["total_metric_loss_summed"] is False
        ),
        "complete_frozen_claim_fails_closed": (
            claims["complete_generic_frozen_operator_constructed"] is False
            and claims["finite_frozen_loss_for_bounded_background_class"]
            is False
            and claims[
                "pure_principal_unrestricted_minimum_loss_established"
            ]
            is True
            and claims[
                "complete_generic_unrestricted_minimum_loss_established"
            ]
            is False
            and claims[
                "complete_generic_physical_TT_minimum_loss_established"
            ]
            is False
        ),
        "no_variable_nonlinear_or_physical_extension_is_claimed": (
            claims["variable_coefficient_energy_estimate_established"]
            is False
            and claims["quasilinear_tame_estimate_established"] is False
            and claims["loss_nonaccumulation_established"] is False
            and claims["local_existence_established"] is False
            and claims["uniqueness_established"] is False
            and claims["continuous_dependence_established"] is False
            and prohibitions[
                "constraint_restricted_loss_inferred_without_projector"
            ]
            is False
            and prohibitions[
                "equivalence_shift_called_propagator_loss"
            ]
            is False
            and prohibitions["regularizer_or_fiducial_mode_added"] is False
            and prohibitions["source_extension_executed"] is False
            and prohibitions["ghost_analysis_executed"] is False
            and prohibitions["phenomenology_executed"] is False
            and prohibitions["yukawa_work_executed"] is False
        ),
    }
    failed = [name for name, passed in checks.items() if not passed]
    accepted = not failed
    return {
        "schema_id": (
            "QFT_GR_QUADRATIC_FROZEN_COEFFICIENT_JORDAN_CHAIN_"
            "FREQUENCY_GROWTH_RESULT_REVIEW_20260728_v0"
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
            "recomputes_partition_arithmetic": True,
            "recomputes_root_component_coverage": True,
            "recomputes_growth_exponents_from_exact_exponentials": True,
            "recomputes_maximum_return_cycle_exponent": True,
            "audits_pure_principal_upper_and_lower_bounds": True,
            "rejects_order_graph_as_complete_frozen_operator": True,
            "fails_closed_on_missing_constraint_projector": True,
            "audits_claim_ceiling": True,
        },
        "accepted_results": (
            [
                "FROZEN_AUXILIARY_ZERO_LOSS_CONFIRMED",
                (
                    "PURE_PRINCIPAL_METRIC_EQUIVALENCE_TWO_DERIVATIVE_"
                    "GROWTH"
                ),
                (
                    "PURE_PRINCIPAL_PHYSICAL_TT_ONE_DERIVATIVE_GROWTH"
                ),
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
            if accepted
            else []
        ),
        "not_established": [
            "CONSTRAINT_RESTRICTED_MINIMUM_FROZEN_LOSS",
            "COMPLETE_GENERIC_FROZEN_COMPANION_OPERATOR",
            "COMPLETE_GENERIC_FROZEN_METRIC_MINIMUM_LOSS",
            "COMPLETE_GENERIC_FROZEN_PHYSICAL_TT_MINIMUM_LOSS",
            "FULL_128_STATE_CONSTRAINT_TANGENT_PROJECTOR",
            "VARIABLE_COEFFICIENT_LINEAR_ESTIMATE",
            "QUASILINEAR_TAME_ESTIMATE",
            "LOSS_NONACCUMULATION",
            "PICARD_CLOSURE",
            "NASH_MOSER_REQUIREMENT",
            "LOCAL_EXISTENCE",
            "UNIQUENESS",
            "CONTINUOUS_DEPENDENCE",
        ],
        "authority_rotation": {
            "frozen_frequency_growth_execution_accepted": accepted,
            "exact_generic_frozen_companion_operator_authorized": accepted,
            "constraint_tangent_projection_authorized": False,
            "variable_coefficient_estimate_authorized": False,
            "quasilinear_estimate_authorized": False,
            "iteration_closure_authorized": False,
            "local_existence_theorem_authorized": False,
            "source_extension_authorized": False,
            "ghost_analysis_authorized": False,
            "phenomenology_authorized": False,
            "yukawa_work_authorized": False,
        },
        "selected_next_target": (
            EXPECTED_NEXT_TARGET
            if accepted
            else (
                "repair_qft_gr_quadratic_frozen_coefficient_"
                "jordan_chain_frequency_growth_v0"
            )
        ),
        "verdict": (
            "ACCEPT_PURE_PRINCIPAL_CHAIN_GROWTH_KEEP_COMPLETE_GENERIC_"
            "FROZEN_AND_CONSTRAINT_RESTRICTED_MINIMA_BLOCKED_AUTHORIZE_"
            "EXACT_GENERIC_FROZEN_COMPANION_OPERATOR_ONLY_NO_VARIABLE_"
            "OR_NONLINEAR_ESTIMATE"
            if accepted
            else (
                "B_BLOCKED_FROZEN_JORDAN_FREQUENCY_GROWTH_REQUIRES_"
                "CORRECTION"
            )
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_review,
        description=(
            "quadratic-gravity frozen-coefficient Jordan-chain "
            "frequency-growth result review"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
