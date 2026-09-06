from __future__ import annotations

from formal.python.toe.calculations import (
    calc_qft_gr_quadratic_full_reduced_system_principal_structure
    as calculation,
)
from formal.python.tools import (
    qft_gr_quadratic_full_reduced_system_principal_structure_result_review
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


def test_variable_order_and_component_count_are_frozen() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    ordering = artifact["variable_and_equation_order"]
    assert ordering["variables"] == ["g_mn", "c_mna", "R", "r_a", "S_mn"]
    assert ordering["equations"] == ["E_g^H", "E_c", "E_R", "E_r", "E_S"]
    assert ordering["component_dimensions"] == {
        "g_mn": 10,
        "c_mna": 40,
        "R": 1,
        "r_a": 4,
        "S_mn": 9,
    }
    assert ordering["total_components"] == 64


def test_equal_order_auxiliary_symbol_is_not_mislabeled_metric_symbol() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    symbol = artifact["ordinary_equal_order_symbol"]
    assert symbol["normalized_pencil"] == "q I_64"
    assert symbol["algebraic_multiplicity_each_root"] == 64
    assert symbol["geometric_multiplicity_each_root"] == 64
    assert symbol["uniform_condition_number"] == 1
    assert symbol["metric_norm_equivalent"] is False
    assert symbol["classification"] == (
        "AUXILIARY_EQUAL_ORDER_SYSTEM_STRONGLY_HYPERBOLIC"
    )


def test_adapted_symbol_has_uniform_complete_wave_basis() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    adapted = artifact["adapted_auxiliary_symbol"]
    assert adapted["weights"] == {
        "g_mn": 2,
        "c_mna": 1,
        "R": 2,
        "r_a": 1,
        "S_mn": 1,
    }
    assert adapted["normalized_weighted_principal_pencil"] == "q I_64"
    assert adapted["uniform_diagonalizer"] == "T_A(khat)=I_64"
    assert adapted["uniform_condition_number"] == 1
    assert adapted["classification"] == (
        "FULL_REDUCED_SYSTEM_STRONGLY_HYPERBOLIC_ONLY_IN_ADAPTED_GRADING"
    )
    assert adapted["energy_estimate_inferred"] is False
    assert adapted["metric_reconstruction_at_same_regularities"] is False


def test_metric_equivalence_symbol_is_triangular_and_defective() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    metric = artifact["metric_equivalence_weighted_symbol"]
    assert metric["weights"] == {
        "g_mn": 3,
        "c_mna": 2,
        "R": 1,
        "r_a": 0,
        "S_mn": 1,
    }
    assert metric["exact_normalized_block_pencil"] == [
        ["q I_10", "0", "u", "0", "2J"],
        ["0", "q I_40", "i ell tensor u", "0", "2i ell tensor J"],
        ["0", "0", "q", "0", "0"],
        ["0", "0", "0", "q I_4", "0"],
        ["0", "0", "0", "-a i H(ell)", "q I_9"],
    ]
    assert metric["generic_classification"] == (
        "FULL_REDUCED_SYSTEM_TRIANGULAR_WITH_FINITE_DERIVATIVE_LOSS"
    )
    assert metric["pointwise_complete_eigenbasis"] is False
    assert metric["uniform_diagonalizer_exists"] is False
    assert metric["finite_equivalence_derivative_loss"] == 1


def test_exact_root_ranks_give_the_recorded_jordan_partition() -> None:
    direct = calculation.derive_exact_rank_data()
    generic = direct["generic_root"]
    assert direct["tracefree_inclusion_rank"] == 9
    assert direct["curvature_to_metric_block_rank"] == 10
    assert generic["algebraic_multiplicity"] == 64
    assert generic["geometric_multiplicity"] == 50
    assert generic["nilpotent_rank"] == 14
    assert generic["nilpotent_square_rank"] == 4
    assert generic["nilpotent_index"] == 3
    assert generic["jordan_blocks_size_3"] == 4
    assert generic["jordan_blocks_size_2"] == 6
    assert generic["jordan_blocks_size_1"] == 40
    assert generic["complete_eigenbasis"] is False
    for sample in direct["directional_exact_samples"].values():
        assert sample["tracefree_hessian_rank"] == 4
        assert sample["root_nilpotent_rank"] == 14
        assert sample["root_nilpotent_square_rank"] == 4
        assert sample["root_nilpotent_cube_is_zero"] is True
        assert sample["root_kernel_dimension"] == 50


def test_two_alpha_plus_beta_control_does_not_remove_defect() -> None:
    direct = calculation.derive_exact_rank_data()
    control = direct["two_alpha_plus_beta_zero_control"]
    assert control == {
        "root_nilpotent_rank": 10,
        "root_nilpotent_square_rank": 0,
        "algebraic_multiplicity": 64,
        "geometric_multiplicity": 54,
        "jordan_blocks_size_2": 10,
        "jordan_blocks_size_1": 44,
        "complete_eigenbasis": False,
    }


def test_physical_spin2_block_survives_differential_elimination() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    physical = artifact["physical_spin2_embedding"]
    assert physical["unnormalized_auxiliary_pencil_per_polarization"] == [
        ["q", "2"],
        ["0", "beta q"],
    ]
    assert physical["two_polarization_multiplicities"] == {
        "algebraic_each_root": 4,
        "geometric_each_root": 2,
    }
    assert physical["recovered_metric_pencil"] == "-beta q^2 I_2"
    assert physical["differential_inverse_is_uniformly_bounded"] is False
    assert physical["physical_defect_repaired"] is False


def test_review_accepts_energy_hierarchy_preparation_only() -> None:
    artifact = read_json(review.OUTPUT_PATH)
    assert artifact["accepted"] is True
    assert artifact["failed_checks"] == []
    assert artifact["selected_next_target"] == review.EXPECTED_NEXT_TARGET
    assert artifact["accepted_results"] == [
        (
            "FULL_REDUCED_SYSTEM_STRONGLY_HYPERBOLIC_"
            "ONLY_IN_ADAPTED_GRADING"
        ),
        "FULL_REDUCED_SYSTEM_TRIANGULAR_WITH_FINITE_DERIVATIVE_LOSS",
        "PHYSICAL_SPIN2_DEFECT_RETAINED",
        "SUBSIDIARY_AND_PHYSICAL_BLOCKS_SEPARATED",
    ]
    rotation = artifact["authority_rotation"]
    assert rotation["full_reduced_principal_structure_accepted"] is True
    assert rotation["energy_hierarchy_preparation_authorized"] is True
    assert rotation["energy_estimate_execution_authorized"] is False
    assert rotation["local_existence_theorem_authorized"] is False
    assert rotation["source_extension_authorized"] is False
    assert all(review.build_review()["checks"].values())


def test_no_energy_or_well_posedness_claim_was_smuggled_in() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    claims = artifact["claim_boundary"]
    assert claims["energy_estimate_established"] is False
    assert claims["loss_nonaccumulation_established"] is False
    assert claims["local_existence_established"] is False
    assert claims["uniqueness_established"] is False
    assert claims["continuous_dependence_established"] is False
    assert claims["source_extension_executed"] is False
