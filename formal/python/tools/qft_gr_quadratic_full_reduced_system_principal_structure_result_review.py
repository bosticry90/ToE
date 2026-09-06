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
    "CALC-QFT-GR-QUADRATIC-FULL-REDUCED-SYSTEM-PRINCIPAL-"
    "STRUCTURE-v0.json"
)
CONSTRAINT_REVIEW_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_GAUGE_AND_AUXILIARY_CONSTRAINT_PROPAGATION_"
    "SYSTEM_RESULT_REVIEW_20260728_v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_FULL_REDUCED_SYSTEM_PRINCIPAL_STRUCTURE_"
    "RESULT_REVIEW_20260728_v0.json"
)
EXPECTED_CURRENT_TARGET = (
    "review_qft_gr_quadratic_full_reduced_system_"
    "principal_structure_v0_result"
)
EXPECTED_NEXT_TARGET = (
    "prepare_qft_gr_quadratic_adapted_derivative_loss_"
    "energy_hierarchy_v0"
)


def _independent_root_rank_reconstruction() -> dict:
    """Rebuild the canonical-direction root matrix without calculation imports."""
    inclusion = sp.zeros(10, 9)
    for index in range(9):
        inclusion[index, index] = 1
    inclusion[9, 0] = 1
    inclusion[9, 4] = -1
    inclusion[9, 7] = -1
    half_metric = sp.zeros(10, 1)
    for row, value in ((0, -1), (4, 1), (7, 1), (9, 1)):
        half_metric[row, 0] = sp.Rational(value, 2)

    def hessian_map(lam: int) -> sp.Matrix:
        ell = sp.Matrix([lam, 1, 0, 0])
        eta = sp.diag(-1, 1, 1, 1)
        columns: list[sp.Matrix] = []
        for index in range(4):
            r = sp.zeros(4, 1)
            r[index, 0] = 1
            symmetric = (ell * r.T + r * ell.T) / 2
            tracefree = symmetric - eta * (eta * symmetric).trace() / 4
            columns.append(
                sp.Matrix(
                    [
                        tracefree[0, 0],
                        tracefree[0, 1],
                        tracefree[0, 2],
                        tracefree[0, 3],
                        tracefree[1, 1],
                        tracefree[1, 2],
                        tracefree[1, 3],
                        tracefree[2, 2],
                        tracefree[2, 3],
                    ]
                )
            )
        return sp.Matrix.hstack(*columns)

    roots: dict[str, dict[str, int | bool]] = {}
    for lam in (-1, 1):
        ell = sp.Matrix([lam, 1, 0, 0])
        hessian = hessian_map(lam)
        nilpotent = sp.zeros(64, 64)
        nilpotent[0:10, 50] = half_metric
        nilpotent[0:10, 55:64] = 2 * inclusion
        for derivative_index in range(4):
            row = 10 + 10 * derivative_index
            nilpotent[row : row + 10, 50] = (
                sp.I * ell[derivative_index] * half_metric
            )
            nilpotent[row : row + 10, 55:64] = (
                2 * sp.I * ell[derivative_index] * inclusion
            )
        nilpotent[55:64, 51:55] = -sp.I * hessian
        roots[str(lam)] = {
            "inclusion_rank": inclusion.rank(),
            "curvature_to_metric_rank": sp.Matrix.hstack(
                half_metric, 2 * inclusion
            ).rank(),
            "hessian_rank": hessian.rank(),
            "nilpotent_rank": nilpotent.rank(),
            "nilpotent_square_rank": (nilpotent**2).rank(),
            "nilpotent_cube_zero": nilpotent**3 == sp.zeros(64, 64),
            "kernel_dimension": 64 - nilpotent.rank(),
        }
    return {
        "roots": roots,
        "jordan_blocks_size_3": 4,
        "jordan_blocks_size_2": 6,
        "jordan_blocks_size_1": 40,
    }


def build_review() -> dict:
    calculation = read_json(CALCULATION_PATH)
    predecessor = read_json(CONSTRAINT_REVIEW_PATH)
    independent = _independent_root_rank_reconstruction()
    order = calculation["variable_and_equation_order"]
    ordinary = calculation["ordinary_equal_order_symbol"]
    adapted = calculation["adapted_auxiliary_symbol"]
    metric = calculation["metric_equivalence_weighted_symbol"]
    physical = calculation["physical_spin2_embedding"]
    separation = calculation["sector_separation"]
    claims = calculation["claim_boundary"]
    prohibitions = calculation["prohibitions_respected"]
    independent_roots = independent["roots"]
    stored_generic = metric["root_rank_data"]["generic_root"]

    checks = {
        "authority_and_predecessor_are_exactly_bound": (
            predecessor["accepted"] is True
            and predecessor["selected_next_target"]
            == calculation["execution_target"]
            and calculation["execution_target"]
            == (
                "compute_qft_gr_quadratic_full_reduced_system_"
                "principal_structure_v0"
            )
            and calculation["selected_next_target"]
            == EXPECTED_CURRENT_TARGET
            and len(calculation["consumed_authority"]["sha256"]) == 64
            and len(calculation["consumed_reduced_system"]["sha256"]) == 64
        ),
        "variable_and_equation_inventory_is_exact": (
            order["variables"] == ["g_mn", "c_mna", "R", "r_a", "S_mn"]
            and order["equations"]
            == ["E_g^H", "E_c", "E_R", "E_r", "E_S"]
            and order["component_dimensions"]
            == {
                "g_mn": 10,
                "c_mna": 40,
                "R": 1,
                "r_a": 4,
                "S_mn": 9,
            }
            and order["total_components"] == 64
        ),
        "ordinary_auxiliary_symbol_is_complete_but_not_metric_equivalent": (
            ordinary["normalized_pencil"] == "q I_64"
            and ordinary["algebraic_multiplicity_each_root"] == 64
            and ordinary["geometric_multiplicity_each_root"] == 64
            and ordinary["uniform_diagonalizer"] == "T(khat)=I_64"
            and ordinary["uniform_condition_number"] == 1
            and ordinary["metric_norm_equivalent"] is False
            and ordinary["classification"]
            == "AUXILIARY_EQUAL_ORDER_SYSTEM_STRONGLY_HYPERBOLIC"
        ),
        "adapted_weights_follow_the_definition_hierarchy": (
            adapted["weights"]
            == {
                "g_mn": 2,
                "c_mna": 1,
                "R": 2,
                "r_a": 1,
                "S_mn": 1,
            }
            and adapted["weighted_orders_of_cross_couplings"]
            == {
                "E_g<-R": 0,
                "E_g<-S": 1,
                "E_c<-R": 0,
                "E_c<-S": 1,
                "E_r<-R": 0,
                "E_S<-r": 1,
            }
            and adapted["normalized_weighted_principal_pencil"] == "q I_64"
            and adapted["uniform_condition_number"] == 1
            and adapted["metric_reconstruction_at_same_regularities"]
            is False
            and adapted["energy_estimate_inferred"] is False
        ),
        "metric_equivalence_weights_expose_one_extra_metric_derivative": (
            metric["weights"]
            == {
                "g_mn": 3,
                "c_mna": 2,
                "R": 1,
                "r_a": 0,
                "S_mn": 1,
            }
            and metric["finite_equivalence_derivative_loss"] == 1
            and metric["exact_normalized_block_pencil"]
            == [
                ["q I_10", "0", "u", "0", "2J"],
                [
                    "0",
                    "q I_40",
                    "i ell tensor u",
                    "0",
                    "2i ell tensor J",
                ],
                ["0", "0", "q", "0", "0"],
                ["0", "0", "0", "q I_4", "0"],
                ["0", "0", "0", "-a i H(ell)", "q I_9"],
            ]
        ),
        "root_ranks_and_jordan_counts_are_independently_reproduced": (
            all(
                root["inclusion_rank"] == 9
                and root["curvature_to_metric_rank"] == 10
                and root["hessian_rank"] == 4
                and root["nilpotent_rank"] == 14
                and root["nilpotent_square_rank"] == 4
                and root["nilpotent_cube_zero"] is True
                and root["kernel_dimension"] == 50
                for root in independent_roots.values()
            )
            and stored_generic["algebraic_multiplicity"] == 64
            and stored_generic["geometric_multiplicity"] == 50
            and stored_generic["jordan_blocks_size_3"]
            == independent["jordan_blocks_size_3"]
            and stored_generic["jordan_blocks_size_2"]
            == independent["jordan_blocks_size_2"]
            and stored_generic["jordan_blocks_size_1"]
            == independent["jordan_blocks_size_1"]
            and stored_generic["complete_eigenbasis"] is False
        ),
        "internal_rank_control_remains_defective": (
            metric["root_rank_data"]["two_alpha_plus_beta_zero_control"]
            == {
                "root_nilpotent_rank": 10,
                "root_nilpotent_square_rank": 0,
                "algebraic_multiplicity": 64,
                "geometric_multiplicity": 54,
                "jordan_blocks_size_2": 10,
                "jordan_blocks_size_1": 44,
                "complete_eigenbasis": False,
            }
        ),
        "physical_spin2_defect_is_exactly_recovered": (
            physical["polarization_count"] == 2
            and physical["unnormalized_auxiliary_pencil_per_polarization"]
            == [["q", "2"], ["0", "beta q"]]
            and physical["two_polarization_multiplicities"]
            == {
                "algebraic_each_root": 4,
                "geometric_each_root": 2,
            }
            and physical["recovered_metric_pencil"] == "-beta q^2 I_2"
            and physical["differential_inverse_is_uniformly_bounded"]
            is False
            and physical["physical_defect_repaired"] is False
        ),
        "directional_uniformity_and_sector_separation_are_explicit": (
            claims["all_nonzero_spatial_directions_covered"] is True
            and claims["adapted_auxiliary_uniform_diagonalizer_established"]
            is True
            and claims["ordinary_metric_uniform_diagonalizer_established"]
            is False
            and metric["pointwise_complete_eigenbasis"] is False
            and metric["uniform_diagonalizer_exists"] is False
            and "defective" in separation["physical_metric_block"]
            and "strongly hyperbolic"
            in separation["subsidiary_constraint_block"]
            and "not metric-norm equivalent"
            in separation["auxiliary_equal_order_block"]
        ),
        "terminal_classification_is_narrow_and_noncontradictory": (
            calculation["terminal_outcomes"]
            == [
                (
                    "FULL_REDUCED_SYSTEM_STRONGLY_HYPERBOLIC_"
                    "ONLY_IN_ADAPTED_GRADING"
                ),
                (
                    "FULL_REDUCED_SYSTEM_TRIANGULAR_WITH_FINITE_"
                    "DERIVATIVE_LOSS"
                ),
            ]
            and claims["ordinary_metric_strong_hyperbolicity_restored"]
            is False
            and claims["finite_derivative_loss_identified"] is True
        ),
        "energy_and_well_posedness_claim_ceiling_is_preserved": (
            claims["energy_estimate_established"] is False
            and claims["loss_nonaccumulation_established"] is False
            and claims["local_existence_established"] is False
            and claims["uniqueness_established"] is False
            and claims["continuous_dependence_established"] is False
            and claims["source_extension_executed"] is False
            and prohibitions["energy_estimate_inferred_from_symbol"] is False
            and prohibitions[
                "differential_transformation_treated_as_bounded_inverse"
            ]
            is False
            and prohibitions["regularizer_or_fiducial_mode_added"] is False
            and prohibitions["yukawa_work_executed"] is False
        ),
    }
    failed = [name for name, passed in checks.items() if not passed]
    accepted = not failed
    return {
        "schema_id": (
            "QFT_GR_QUADRATIC_FULL_REDUCED_SYSTEM_PRINCIPAL_"
            "STRUCTURE_RESULT_REVIEW_20260728_v0"
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
            "reconstructs_tracefree_inclusion": True,
            "reconstructs_tracefree_hessian_map": True,
            "reconstructs_64_component_root_matrix": True,
            "recomputes_nilpotent_ranks": True,
            "recomputes_jordan_counts": True,
            "audits_derivative_weights": True,
            "audits_physical_elimination": True,
            "audits_claim_ceiling": True,
        },
        "accepted_results": (
            [
                (
                    "FULL_REDUCED_SYSTEM_STRONGLY_HYPERBOLIC_"
                    "ONLY_IN_ADAPTED_GRADING"
                ),
                (
                    "FULL_REDUCED_SYSTEM_TRIANGULAR_WITH_FINITE_"
                    "DERIVATIVE_LOSS"
                ),
                "PHYSICAL_SPIN2_DEFECT_RETAINED",
                "SUBSIDIARY_AND_PHYSICAL_BLOCKS_SEPARATED",
            ]
            if accepted
            else []
        ),
        "not_established": [
            "STANDARD_METRIC_STRONG_HYPERBOLICITY",
            "STANDARD_METRIC_UNIFORM_SYMMETRIZER",
            "ADAPTED_LINEAR_ENERGY_ESTIMATE",
            "DERIVATIVE_LOSS_NONACCUMULATION",
            "PICARD_OR_NASH_MOSER_CLOSURE",
            "LOCAL_EXISTENCE",
            "UNIQUENESS",
            "CONTINUOUS_DEPENDENCE",
            "SOURCE_EXTENSION_ADMISSIBILITY",
        ],
        "authority_rotation": {
            "full_reduced_principal_structure_accepted": accepted,
            "energy_hierarchy_preparation_authorized": accepted,
            "energy_estimate_execution_authorized": False,
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
                "repair_qft_gr_quadratic_full_reduced_system_"
                "principal_structure_v0"
            )
        ),
        "verdict": (
            "ACCEPT_ADAPTED_AUXILIARY_WAVE_DIAGONALIZATION_AND_METRIC_"
            "EQUIVALENCE_TRIANGULAR_DEFECT_WITH_FIXED_ONE_DERIVATIVE_"
            "LOSS_AUTHORIZE_ENERGY_HIERARCHY_PREPARATION_ONLY"
            if accepted
            else (
                "B_BLOCKED_FULL_REDUCED_PRINCIPAL_STRUCTURE_REQUIRES_"
                "CORRECTION"
            )
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_review,
        description=(
            "quadratic-gravity full reduced-system principal-structure "
            "result review"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
