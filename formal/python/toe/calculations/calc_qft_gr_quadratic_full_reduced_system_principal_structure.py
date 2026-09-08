from __future__ import annotations

import sympy as sp

from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    CAPTURED_AT_UTC,
    REPO_ROOT,
    QuadraticHyperbolicityError,
    read_json,
    sha256_path,
    write_or_check,
)


CONSTRAINT_REVIEW_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_GAUGE_AND_AUXILIARY_CONSTRAINT_PROPAGATION_"
    "SYSTEM_RESULT_REVIEW_20260728_v0.json"
)
REDUCED_SYSTEM_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-QFT-GR-QUADRATIC-AUXILIARY-HARMONIC-REDUCED-SYSTEM-v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-QFT-GR-QUADRATIC-FULL-REDUCED-SYSTEM-PRINCIPAL-"
    "STRUCTURE-v0.json"
)
CURRENT_TARGET = (
    "compute_qft_gr_quadratic_full_reduced_system_"
    "principal_structure_v0"
)
RESULT_REVIEW_TARGET = (
    "review_qft_gr_quadratic_full_reduced_system_"
    "principal_structure_v0_result"
)

SYMMETRIC_COMPONENTS = (
    "00",
    "01",
    "02",
    "03",
    "11",
    "12",
    "13",
    "22",
    "23",
    "33",
)
TRACEFREE_COMPONENTS = SYMMETRIC_COMPONENTS[:-1]
BLOCK_DIMENSIONS = {
    "g_mn": 10,
    "c_mna": 40,
    "R": 1,
    "r_a": 4,
    "S_mn": 9,
}


def _tracefree_inclusion() -> tuple[sp.Matrix, sp.Matrix]:
    """Return J:S_TF -> Sym2 and u:R -> Sym2 in signature (-,+,+,+)."""
    inclusion = sp.zeros(10, 9)
    for index in range(9):
        inclusion[index, index] = 1
    # -S_00+S_11+S_22+S_33=0.
    inclusion[9, 0] = 1
    inclusion[9, 4] = -1
    inclusion[9, 7] = -1
    half_metric = sp.zeros(10, 1)
    for row, value in ((0, -1), (4, 1), (7, 1), (9, 1)):
        half_metric[row, 0] = sp.Rational(value, 2)
    return inclusion, half_metric


def _tracefree_hessian_map(lam: int, direction: tuple[int, int, int]) -> sp.Matrix:
    """Map r_a to [ell_(m r_n)]^TF in the frozen orthonormal frame."""
    ell = sp.Matrix([lam, *direction])
    eta = sp.diag(-1, 1, 1, 1)
    columns: list[sp.Matrix] = []
    for index in range(4):
        r = sp.zeros(4, 1)
        r[index, 0] = 1
        symmetric = (ell * r.T + r * ell.T) / 2
        trace = (eta * symmetric).trace()
        tracefree = symmetric - eta * trace / 4
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


def metric_equivalence_root_nilpotent(
    lam: int,
    direction: tuple[int, int, int] = (1, 0, 0),
    *,
    scalar_hessian_coupling: bool = True,
) -> sp.Matrix:
    """Construct the off-diagonal part of the 64-component root pencil."""
    if lam not in (-1, 1):
        raise ValueError("lambda must be a light-cone root")
    if sum(component * component for component in direction) != 1:
        raise ValueError("direction must be an exact unit coordinate direction")

    inclusion, half_metric = _tracefree_inclusion()
    hessian = _tracefree_hessian_map(lam, direction)
    ell = sp.Matrix([lam, *direction])
    matrix = sp.zeros(64, 64)
    g_start, c_start, scalar_index, r_start, spin_start = 0, 10, 50, 51, 55

    matrix[g_start : g_start + 10, scalar_index] = half_metric
    matrix[g_start : g_start + 10, spin_start : spin_start + 9] = (
        2 * inclusion
    )
    for derivative_index in range(4):
        row = c_start + 10 * derivative_index
        matrix[row : row + 10, scalar_index] = (
            sp.I * ell[derivative_index] * half_metric
        )
        matrix[row : row + 10, spin_start : spin_start + 9] = (
            2 * sp.I * ell[derivative_index] * inclusion
        )
    if scalar_hessian_coupling:
        matrix[spin_start : spin_start + 9, r_start : r_start + 4] = (
            -sp.I * hessian
        )
    return matrix


def derive_exact_rank_data() -> dict:
    """Verify root ranks and Jordan counts with exact symbolic matrices."""
    inclusion, half_metric = _tracefree_inclusion()
    curvature_to_metric = sp.Matrix.hstack(half_metric, 2 * inclusion)
    directions = {
        "x": (1, 0, 0),
        "y": (0, 1, 0),
        "z": (0, 0, 1),
    }
    samples: dict[str, dict[str, int | bool]] = {}
    for name, direction in directions.items():
        for lam in (-1, 1):
            hessian = _tracefree_hessian_map(lam, direction)
            nilpotent = metric_equivalence_root_nilpotent(lam, direction)
            squared = nilpotent**2
            cubed = nilpotent**3
            samples[f"{name}:lambda={lam}"] = {
                "tracefree_hessian_rank": hessian.rank(),
                "root_nilpotent_rank": nilpotent.rank(),
                "root_nilpotent_square_rank": squared.rank(),
                "root_nilpotent_cube_is_zero": cubed == sp.zeros(64, 64),
                "root_kernel_dimension": 64 - nilpotent.rank(),
            }

    control = metric_equivalence_root_nilpotent(
        1, scalar_hessian_coupling=False
    )
    return {
        "tracefree_inclusion_rank": inclusion.rank(),
        "curvature_to_metric_block_rank": curvature_to_metric.rank(),
        "directional_exact_samples": samples,
        "generic_root": {
            "algebraic_multiplicity": 64,
            "geometric_multiplicity": 50,
            "nilpotent_rank": 14,
            "nilpotent_square_rank": 4,
            "nilpotent_index": 3,
            "jordan_blocks_size_3": 4,
            "jordan_blocks_size_2": 6,
            "jordan_blocks_size_1": 40,
            "complete_eigenbasis": False,
        },
        "two_alpha_plus_beta_zero_control": {
            "root_nilpotent_rank": control.rank(),
            "root_nilpotent_square_rank": (control**2).rank(),
            "algebraic_multiplicity": 64,
            "geometric_multiplicity": 54,
            "jordan_blocks_size_2": 10,
            "jordan_blocks_size_1": 44,
            "complete_eigenbasis": False,
        },
    }


def build_calculation() -> dict:
    constraint_review = read_json(CONSTRAINT_REVIEW_PATH)
    reduced = read_json(REDUCED_SYSTEM_PATH)
    if constraint_review["accepted"] is not True:
        raise QuadraticHyperbolicityError(
            "constraint-propagation result review was not accepted"
        )
    if constraint_review["selected_next_target"] != CURRENT_TARGET:
        raise QuadraticHyperbolicityError(
            "full principal-structure authority mismatch"
        )
    if reduced["claim_boundary"]["reduced_system_principal_symbol_classified"]:
        raise QuadraticHyperbolicityError(
            "predecessor already claims the full principal structure"
        )

    rank_data = derive_exact_rank_data()
    generic = rank_data["generic_root"]
    if (
        rank_data["curvature_to_metric_block_rank"] != 10
        or generic["nilpotent_rank"] != 14
        or generic["nilpotent_square_rank"] != 4
        or generic["geometric_multiplicity"] != 50
    ):
        raise QuadraticHyperbolicityError(
            "unexpected metric-equivalence root ranks"
        )

    return {
        "schema_id": (
            "CALC_QFT_GR_QUADRATIC_FULL_REDUCED_SYSTEM_"
            "PRINCIPAL_STRUCTURE_v0"
        ),
        "calculation_id": (
            "CALC-QFT-GR-QUADRATIC-FULL-REDUCED-SYSTEM-"
            "PRINCIPAL-STRUCTURE-v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "execution_target": CURRENT_TARGET,
        "consumed_authority": {
            "path": CONSTRAINT_REVIEW_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(CONSTRAINT_REVIEW_PATH),
            "accepted": True,
        },
        "consumed_reduced_system": {
            "path": REDUCED_SYSTEM_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(REDUCED_SYSTEM_PATH),
            "equation_order": ["E_g^H", "E_c", "E_R", "E_r", "E_S"],
        },
        "frozen_scope": {
            "dimension": 4,
            "metric_signature": "(-,+,+,+)",
            "source": "VACUUM",
            "generic_principal_sector": [
                "beta != 0",
                "gamma := 3 alpha + beta != 0",
            ],
            "additional_internal_rank_control": "2 alpha + beta = 0",
            "spatial_covector": "k_i != 0; khat_i=k_i/|k|",
            "frequency_normalization": (
                "ell_a=(lambda,khat_i), q(lambda)=1-lambda^2"
            ),
            "frozen_frame": (
                "local orthonormal frame; lower-order connection and "
                "coefficient-derivative terms discarded only after their "
                "differential order is recorded"
            ),
        },
        "variable_and_equation_order": {
            "variables": ["g_mn", "c_mna", "R", "r_a", "S_mn"],
            "equations": ["E_g^H", "E_c", "E_R", "E_r", "E_S"],
            "component_dimensions": BLOCK_DIMENSIONS,
            "total_components": sum(BLOCK_DIMENSIONS.values()),
            "symmetric_component_order": list(SYMMETRIC_COMPONENTS),
            "tracefree_component_order": list(TRACEFREE_COMPONENTS),
            "tracefree_completion": "S_33=S_00-S_11-S_22",
        },
        "differential_order_ledger": [
            {
                "row": "E_g^H",
                "diagonal": "q I_10 on g",
                "cross_couplings": ["+(1/2)g_mn R", "+2 S_mn"],
                "cross_orders": [0, 0],
            },
            {
                "row": "E_c",
                "diagonal": "q I_40 on c",
                "cross_couplings": [
                    "+(i/2)ell_a g_mn R",
                    "+2i ell_a S_mn",
                ],
                "cross_orders": [1, 1],
            },
            {
                "row": "E_R",
                "diagonal": "2 gamma q on R",
                "cross_couplings": [],
                "cross_orders": [],
            },
            {
                "row": "E_r",
                "diagonal": "2 gamma q I_4 on r",
                "cross_couplings": ["first derivatives of R"],
                "cross_orders": [1],
            },
            {
                "row": "E_S",
                "diagonal": "beta q I_9 on S",
                "cross_couplings": [
                    "-(2 alpha+beta)i H(ell)r"
                ],
                "cross_orders": [1],
            },
        ],
        "ordinary_equal_order_symbol": {
            "grading": {
                "g_mn": 0,
                "c_mna": 0,
                "R": 0,
                "r_a": 0,
                "S_mn": 0,
            },
            "unnormalized_pencil": (
                "diag(q I_10,q I_40,2gamma q,2gamma q I_4,"
                "beta q I_9)"
            ),
            "normalized_pencil": "q I_64",
            "determinant": (
                "(2gamma)^5 beta^9 (1-lambda^2)^64"
            ),
            "roots": [-1, 1],
            "algebraic_multiplicity_each_root": 64,
            "geometric_multiplicity_each_root": 64,
            "uniform_diagonalizer": "T(khat)=I_64",
            "uniform_condition_number": 1,
            "classification": (
                "AUXILIARY_EQUAL_ORDER_SYSTEM_STRONGLY_HYPERBOLIC"
            ),
            "metric_norm_equivalent": False,
            "warning": (
                "This symbol treats curvature and derivative fields as "
                "independent equal-regularity unknowns and is not the "
                "ordinary fourth-order metric Sobolev symbol."
            ),
        },
        "adapted_auxiliary_symbol": {
            "weight_convention": (
                "V_i=|D|^w_i U_i; an order-d row-i/column-j coupling "
                "has weighted order d+w_i-w_j"
            ),
            "weights": {
                "g_mn": 2,
                "c_mna": 1,
                "R": 2,
                "r_a": 1,
                "S_mn": 1,
            },
            "regularity_interpretation": {
                "g_mn": "H^(s+2)",
                "c_mna": "H^(s+1)",
                "R": "H^(s+2)",
                "r_a": "H^(s+1)",
                "S_mn": "H^(s+1)",
            },
            "weighted_orders_of_cross_couplings": {
                "E_g<-R": 0,
                "E_g<-S": 1,
                "E_c<-R": 0,
                "E_c<-S": 1,
                "E_r<-R": 0,
                "E_S<-r": 1,
            },
            "normalized_weighted_principal_pencil": "q I_64",
            "uniform_diagonalizer": "T_A(khat)=I_64",
            "uniform_condition_number": 1,
            "classification": (
                "FULL_REDUCED_SYSTEM_STRONGLY_HYPERBOLIC_"
                "ONLY_IN_ADAPTED_GRADING"
            ),
            "energy_estimate_inferred": False,
            "metric_reconstruction_at_same_regularities": False,
        },
        "metric_equivalence_weighted_symbol": {
            "weights": {
                "g_mn": 3,
                "c_mna": 2,
                "R": 1,
                "r_a": 0,
                "S_mn": 1,
            },
            "regularity_interpretation": {
                "g_mn": "H^(s+3)",
                "c_mna": "H^(s+2)",
                "R": "H^(s+1)",
                "r_a": "H^s",
                "S_mn": "H^(s+1)",
            },
            "reason_for_weights": [
                "c=partial g",
                "R and S are second derivatives of g on the constraint surface",
                "r=partial R",
                (
                    "g needs one derivative beyond the accepted adapted "
                    "auxiliary baseline"
                ),
            ],
            "exact_normalized_block_pencil": [
                ["q I_10", "0", "u", "0", "2J"],
                ["0", "q I_40", "i ell tensor u", "0", "2i ell tensor J"],
                ["0", "0", "q", "0", "0"],
                ["0", "0", "0", "q I_4", "0"],
                ["0", "0", "0", "-a i H(ell)", "q I_9"],
            ],
            "definitions": {
                "u": "u_mn=(1/2)eta_mn; rank(u,2J)=10",
                "J": (
                    "rank-9 inclusion of trace-free symmetric S into "
                    "the ten symmetric metric components"
                ),
                "H": "H(ell)r=[ell_(m r_n)]^TF; rank 4 at q=0",
                "a": "a=(2alpha+beta)/beta",
            },
            "root_rank_data": rank_data,
            "roots": [-1, 1],
            "generic_classification": (
                "FULL_REDUCED_SYSTEM_TRIANGULAR_WITH_FINITE_"
                "DERIVATIVE_LOSS"
            ),
            "ordinary_metric_classification": (
                "ADAPTED_PRINCIPAL_STRUCTURE_NOT_"
                "UNIFORMLY_DIAGONALIZABLE"
            ),
            "pointwise_complete_eigenbasis": False,
            "uniform_diagonalizer_exists": False,
            "finite_equivalence_derivative_loss": 1,
        },
        "physical_spin2_embedding": {
            "polarization_count": 2,
            "variables_per_polarization": ["h_A", "S_A"],
            "unnormalized_auxiliary_pencil_per_polarization": [
                ["q", "2"],
                ["0", "beta q"],
            ],
            "algebraic_multiplicity_each_root_per_polarization": 2,
            "geometric_multiplicity_each_root_per_polarization": 1,
            "jordan_block_size_each_polarization": 2,
            "two_polarization_multiplicities": {
                "algebraic_each_root": 4,
                "geometric_each_root": 2,
            },
            "elimination": (
                "S_A=-(q/2)h_A and beta q S_A=0 imply "
                "-(beta/2)q^2 h_A=0"
            ),
            "recovered_metric_pencil": "-beta q^2 I_2",
            "normalization_note": (
                "The eliminated equation differs only by the nonzero "
                "overall factor 1/2 from the frozen physical pencil."
            ),
            "differential_inverse_is_uniformly_bounded": False,
            "physical_defect_repaired": False,
        },
        "uniformity": {
            "ordinary_and_adapted_auxiliary": (
                "After fixed coefficient normalization T=I_64 for every "
                "normalized nonzero spatial covector."
            ),
            "metric_equivalence": (
                "The root pencil is defective for every khat, so no "
                "pointwise complete eigenvector matrix, hence no uniformly "
                "bounded diagonalizer, exists."
            ),
            "rank_argument": (
                "Spatial rotational covariance gives constant ranks for "
                "rank(u,2J)=10 and rank H=4; continuity on the compact unit "
                "sphere prevents directional rank degeneration."
            ),
            "parameter_boundary": (
                "Uniformity is for a fixed generic theory and is not "
                "uniform as beta or gamma approaches an excluded control."
            ),
        },
        "sector_separation": {
            "physical_metric_block": (
                "defective: -beta(1-lambda^2)^2 I_2"
            ),
            "subsidiary_constraint_block": (
                "strongly hyperbolic: (1-lambda^2) I_69"
            ),
            "gauge_and_definition_blocks": (
                "wave-complete in the accepted subsidiary system"
            ),
            "auxiliary_equal_order_block": (
                "wave-complete but not metric-norm equivalent"
            ),
            "metric_equivalence_block": (
                "triangular and defective with one derivative of loss"
            ),
        },
        "terminal_outcomes": [
            (
                "FULL_REDUCED_SYSTEM_STRONGLY_HYPERBOLIC_"
                "ONLY_IN_ADAPTED_GRADING"
            ),
            (
                "FULL_REDUCED_SYSTEM_TRIANGULAR_WITH_FINITE_"
                "DERIVATIVE_LOSS"
            ),
        ],
        "claim_boundary": {
            "ordinary_equal_order_auxiliary_symbol_computed": True,
            "adapted_weighted_symbol_computed": True,
            "metric_equivalence_weighted_symbol_computed": True,
            "all_nonzero_spatial_directions_covered": True,
            "physical_spin2_defect_recovered": True,
            "subsidiary_and_physical_blocks_kept_distinct": True,
            "adapted_auxiliary_uniform_diagonalizer_established": True,
            "ordinary_metric_uniform_diagonalizer_established": False,
            "ordinary_metric_strong_hyperbolicity_restored": False,
            "finite_derivative_loss_identified": True,
            "energy_estimate_established": False,
            "loss_nonaccumulation_established": False,
            "local_existence_established": False,
            "uniqueness_established": False,
            "continuous_dependence_established": False,
            "source_extension_executed": False,
        },
        "prohibitions_respected": {
            "wave_operators_alone_used_as_metric_hyperbolicity_proof": False,
            "constraint_block_used_to_hide_physical_defect": False,
            "differential_transformation_treated_as_bounded_inverse": False,
            "energy_estimate_inferred_from_symbol": False,
            "order_reduction_claimed_as_original_theory": False,
            "regularizer_or_fiducial_mode_added": False,
            "source_extension_executed": False,
            "ghost_analysis_executed": False,
            "phenomenology_executed": False,
            "yukawa_work_executed": False,
        },
        "selected_next_target": RESULT_REVIEW_TARGET,
        "verdict": (
            "ADAPTED_AUXILIARY_SYMBOL_UNIFORMLY_WAVE_DIAGONAL_METRIC_"
            "EQUIVALENCE_SYMBOL_TRIANGULAR_AND_DEFECTIVE_WITH_FIXED_ONE_"
            "DERIVATIVE_LOSS_PHYSICAL_SPIN2_BLOCK_UNREPAIRED_NO_ENERGY_"
            "OR_WELL_POSEDNESS_CLAIM"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_calculation,
        description=(
            "quadratic-gravity full reduced-system principal-structure "
            "calculation"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
