from __future__ import annotations

from itertools import permutations

import sympy as sp

from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    CAPTURED_AT_UTC,
    REPO_ROOT,
    QuadraticHyperbolicityError,
    read_json,
    sha256_path,
    write_or_check,
)


ENERGY_REVIEW_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_ADAPTED_DERIVATIVE_LOSS_ENERGY_HIERARCHY_"
    "RESULT_REVIEW_20260728_v0.json"
)
ENERGY_PACKET_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_ADAPTED_DERIVATIVE_LOSS_ENERGY_HIERARCHY_"
    "20260728_v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-QFT-GR-QUADRATIC-FROZEN-COEFFICIENT-JORDAN-CHAIN-"
    "FREQUENCY-GROWTH-v0.json"
)
CURRENT_TARGET = (
    "compute_qft_gr_quadratic_frozen_coefficient_"
    "jordan_chain_frequency_growth_v0"
)
RESULT_REVIEW_TARGET = (
    "review_qft_gr_quadratic_frozen_coefficient_"
    "jordan_chain_frequency_growth_v0_result"
)

COMPONENT_DIMENSIONS = {
    "g_mn": 10,
    "c_mna": 40,
    "R": 1,
    "r_a": 4,
    "S_mn": 9,
}
CHAIN_PARTITION = (3,) * 4 + (2,) * 6 + (1,) * 40


def nilpotent_block(length: int) -> sp.Matrix:
    if length < 1:
        raise ValueError("a Jordan-chain length must be positive")
    matrix = sp.zeros(length)
    for index in range(length - 1):
        matrix[index, index + 1] = 1
    return matrix


def second_order_wave_companion(
    length: int,
    rho: sp.Expr,
) -> sp.Matrix:
    """Return the exact energy-scaled real companion for one chain.

    The state is (rho*u, dt*u).  In a root-chain basis the second-order
    principal equation is

        dt^2 u + rho^2 (I-N) u = 0.

    Its two light-cone roots have a Jordan chain of the requested length.
    """
    identity = sp.eye(length)
    zero = sp.zeros(length)
    nilpotent = nilpotent_block(length)
    return sp.Matrix.vstack(
        sp.Matrix.hstack(zero, rho * identity),
        sp.Matrix.hstack(-rho * (identity - nilpotent), zero),
    )


def root_modal_generator(
    length: int,
    root: int,
    rho: sp.Expr,
    *,
    edge_power: int,
) -> sp.Matrix:
    """Return the exact root-modal growth model for a weighted chain."""
    if root not in (-1, 1):
        raise ValueError("root must be -1 or +1")
    return (
        sp.I * root * rho * sp.eye(length)
        + rho**edge_power * nilpotent_block(length)
    )


def companion_partition_checks() -> dict:
    rho = sp.Integer(2)
    per_length: dict[str, dict[str, int | str]] = {}
    for length in (1, 2, 3):
        companion = second_order_wave_companion(length, rho)
        row: dict[str, int | str] = {
            "state_dimension": 2 * length,
            "characteristic_polynomial": sp.sstr(
                sp.factor(companion.charpoly().as_expr())
            ),
        }
        for root in (-1, 1):
            shifted = companion - sp.I * root * rho * sp.eye(2 * length)
            row[f"lambda_{root}_kernel_dimension"] = (
                2 * length - shifted.rank()
            )
            row[f"lambda_{root}_square_kernel_dimension"] = (
                2 * length - (shifted**2).rank()
            )
            row[f"lambda_{root}_cube_kernel_dimension"] = (
                2 * length - (shifted**3).rank()
            )
        per_length[str(length)] = row
    return {
        "component_count": sum(COMPONENT_DIMENSIONS.values()),
        "first_order_state_count": 2 * sum(COMPONENT_DIMENSIONS.values()),
        "chain_count_each_root": len(CHAIN_PARTITION),
        "chain_partition_each_root": {
            "length_3": CHAIN_PARTITION.count(3),
            "length_2": CHAIN_PARTITION.count(2),
            "length_1": CHAIN_PARTITION.count(1),
        },
        "algebraic_dimension_each_root": sum(CHAIN_PARTITION),
        "geometric_dimension_each_root": len(CHAIN_PARTITION),
        "eigenvector_deficit_each_root": sum(
            length - 1 for length in CHAIN_PARTITION
        ),
        "exact_single_chain_companion_checks_at_rho_2": per_length,
    }


def map_all_chains(packet: dict) -> dict:
    roots: dict[str, list[dict[str, object]]] = {}
    for root in ("-1", "1"):
        cursor = 0
        mapped: list[dict[str, object]] = []
        for chain in packet["jordan_chain_ledger"]["roots"][root]:
            length = int(chain["chain_length"])
            mapped.append(
                {
                    "chain_id": chain["chain_id"],
                    "chain_length": length,
                    "leading_mode": chain["leading_mode"],
                    "root_component_range": [cursor, cursor + length - 1],
                    "companion_position_range": [
                        cursor,
                        cursor + length - 1,
                    ],
                    "companion_velocity_range": [
                        64 + cursor,
                        64 + cursor + length - 1,
                    ],
                    "unrestricted_metric_growth_exponent": length - 1,
                    "adapted_auxiliary_growth_exponent": 0,
                    "constraint_status_from_predecessor": (
                        chain["constraint_status"]
                    ),
                }
            )
            cursor += length
        if cursor != 64 or len(mapped) != 50:
            raise QuadraticHyperbolicityError(
                f"incomplete companion chain map at root {root}"
            )
        roots[root] = mapped
    return {
        "state_order": (
            "(rho W U_1,...,rho W U_64,"
            "W partial_t U_1,...,W partial_t U_64)"
        ),
        "physical_variable_order_before_chain_similarity": [
            "g_mn[10]",
            "c_mna[40]",
            "R[1]",
            "r_a[4]",
            "S_mn[9]",
        ],
        "chain_similarity_note": (
            "The accepted root-dependent Jordan similarity only reorders "
            "and combines the 64 weighted field components; the displayed "
            "position and velocity ranges are exact in that chain basis."
        ),
        "roots": roots,
    }


def metric_weighted_order_edges() -> list[dict[str, int | str]]:
    """Inventory every linearized frozen coupling by its maximum order.

    The raw-order bounds follow directly from the exact reduced equations:
    Q^H is algebraic in (g,c), E_c differentiates Q^H,R,S once, E_R is
    algebraic in (g,c,R,r), E_r differentiates E_R once, and E_S contains
    at most first derivatives of (c,r,S).
    """
    return [
        {"source": "c", "target": "g", "raw_order": 0, "weighted_order": 1},
        {"source": "R", "target": "g", "raw_order": 0, "weighted_order": 2},
        {"source": "S", "target": "g", "raw_order": 0, "weighted_order": 2},
        {"source": "g", "target": "c", "raw_order": 1, "weighted_order": 0},
        {"source": "c", "target": "c", "raw_order": 1, "weighted_order": 1},
        {"source": "R", "target": "c", "raw_order": 1, "weighted_order": 2},
        {"source": "S", "target": "c", "raw_order": 1, "weighted_order": 2},
        {"source": "g", "target": "R", "raw_order": 0, "weighted_order": -2},
        {"source": "c", "target": "R", "raw_order": 0, "weighted_order": -1},
        {"source": "R", "target": "R", "raw_order": 0, "weighted_order": 0},
        {"source": "r", "target": "R", "raw_order": 0, "weighted_order": 1},
        {"source": "g", "target": "r", "raw_order": 0, "weighted_order": -3},
        {"source": "c", "target": "r", "raw_order": 1, "weighted_order": -1},
        {"source": "R", "target": "r", "raw_order": 1, "weighted_order": 0},
        {"source": "r", "target": "r", "raw_order": 1, "weighted_order": 1},
        {"source": "g", "target": "S", "raw_order": 0, "weighted_order": -2},
        {"source": "c", "target": "S", "raw_order": 1, "weighted_order": 0},
        {"source": "R", "target": "S", "raw_order": 0, "weighted_order": 0},
        {"source": "r", "target": "S", "raw_order": 1, "weighted_order": 2},
        {"source": "S", "target": "S", "raw_order": 1, "weighted_order": 1},
    ]


def simple_cycle_exponents(edges: list[dict[str, int | str]]) -> list[dict]:
    nodes = ("g", "c", "R", "r", "S")
    lookup = {
        (str(row["source"]), str(row["target"])): int(
            row["weighted_order"]
        )
        - 1
        for row in edges
    }
    cycles: dict[tuple[str, ...], int] = {}
    for length in range(1, len(nodes) + 1):
        for sequence in permutations(nodes, length):
            links = list(zip(sequence, sequence[1:] + sequence[:1]))
            if not all(link in lookup for link in links):
                continue
            rotations = [
                sequence[index:] + sequence[:index]
                for index in range(length)
            ]
            key = min(rotations)
            cycles[key] = sum(lookup[link] for link in links)
    return [
        {
            "cycle": "->".join((*cycle, cycle[0])),
            "generator_frequency_exponent_sum": exponent,
        }
        for cycle, exponent in sorted(cycles.items())
    ]


def growth_ledger() -> dict:
    edges = metric_weighted_order_edges()
    cycles = simple_cycle_exponents(edges)
    maximum_cycle_sum = max(
        row["generator_frequency_exponent_sum"] for row in cycles
    )
    if maximum_cycle_sum > 0:
        raise QuadraticHyperbolicityError(
            "positive return cycle permits unresolved root splitting"
        )

    rho, time = sp.symbols("rho time", positive=True, real=True)
    exact_modal_exponentials: dict[str, dict[str, str]] = {}
    for length in (1, 2, 3):
        metric_generator = root_modal_generator(
            length,
            1,
            rho,
            edge_power=1,
        )
        adapted_generator = root_modal_generator(
            length,
            1,
            rho,
            edge_power=0,
        )
        exact_modal_exponentials[str(length)] = {
            "metric_equivalence": sp.sstr(
                sp.simplify(sp.exp(time * metric_generator))
            ),
            "adapted_auxiliary": sp.sstr(
                sp.simplify(sp.exp(time * adapted_generator))
            ),
            "metric_minimum_growth_exponent": str(length - 1),
            "adapted_minimum_growth_exponent": "0",
            "saturating_component": (
                f"(rho*time)^{length - 1}/{sp.factorial(length - 1)}"
            ),
        }

    return {
        "exact_root_modal_exponentials": exact_modal_exponentials,
        "metric_generator_edge_rule": (
            "a weighted second-order coupling of order p contributes "
            "rho^(p-1) to the energy-scaled first-order companion"
        ),
        "complete_metric_weighted_linearized_edge_inventory": [
            {
                **row,
                "generator_frequency_exponent": (
                    int(row["weighted_order"]) - 1
                ),
            }
            for row in edges
        ],
        "simple_return_cycles": cycles,
        "maximum_return_cycle_exponent_sum": maximum_cycle_sum,
        "order_screen_conclusion": (
            "No positive-frequency return cycle appears in the block-level "
            "differential-order graph. This is a necessary structural "
            "screen only. It does not replace the exact background-jet "
            "linearization, its 128 by 128 coefficient matrices, or their "
            "conjugation into the root-chain basis, so it cannot exclude "
            "subprincipal root splitting for the complete frozen operator."
        ),
        "subprincipal_sensitivity_controls": [
            {
                "chain": "J_2",
                "forbidden_positive_return_model": (
                    "i lambda rho I + rho N_2 + b E_21"
                ),
                "root_shift": "delta^2=b rho",
                "growth_if_present": "exp(c rho^(1/2) t)",
                "actual_order_graph_status": (
                    "not exhibited by the block-order screen; exclusion "
                    "requires the exact frozen coefficient matrix"
                ),
            },
            {
                "chain": "J_3",
                "forbidden_positive_return_model": (
                    "i lambda rho I + rho N_3 + b E_31"
                ),
                "root_shift": "delta^3=b rho^2",
                "growth_if_present": "exp(c rho^(2/3) t)",
                "actual_order_graph_status": (
                    "not exhibited by the block-order screen; exclusion "
                    "requires the exact frozen coefficient matrix"
                ),
            },
        ],
        "upper_and_lower_bound_contract": {
            "upper": (
                "For each chain of length m, "
                "||G(t,rho)||<=C_T(1+rho)^(m-1)."
            ),
            "lower": (
                "Choose the terminal generalized vector and any fixed "
                "0<t_0<=T. The first chain component contains "
                "(rho t_0)^(m-1)/(m-1)!, so a uniform bound with a smaller "
                "integer exponent is impossible."
            ),
            "uniform_in_roots_for_pure_principal_chains": True,
            "uniform_in_direction_for_pure_principal_chains": True,
        },
        "complete_generic_frozen_operator": {
            "constructed": False,
            "missing_matrices": [
                (
                    "the exact background-jet linearization B_0("
                    "Ubar,partial Ubar,khat) of every lower-order term"
                ),
                (
                    "the exact 128-state conjugation of B_0 into the "
                    "root-chain companion basis at lambda=+1 and -1"
                ),
                (
                    "the exact full-constraint tangent projector and its "
                    "intertwining relation with the frozen companion"
                ),
            ],
            "consequence": (
                "The pure-principal polynomial growth is exact, but the "
                "minimum loss of the complete generic frozen metric "
                "operator remains blocked. In particular, the order graph "
                "alone cannot rule out background-dependent fractional "
                "root splitting or prove a finite Sobolev-loss bound."
            ),
        },
    }


def build_calculation() -> dict:
    review = read_json(ENERGY_REVIEW_PATH)
    packet = read_json(ENERGY_PACKET_PATH)
    if review["accepted"] is not True:
        raise QuadraticHyperbolicityError(
            "energy-hierarchy result review was not accepted"
        )
    if review["selected_next_target"] != CURRENT_TARGET:
        raise QuadraticHyperbolicityError(
            "frozen-frequency-growth authority mismatch"
        )
    if packet["claim_boundary"][
        "frozen_coefficient_energy_estimate_established"
    ]:
        raise QuadraticHyperbolicityError(
            "predecessor already claims the frozen estimate"
        )

    checks = companion_partition_checks()
    if checks["first_order_state_count"] != 128:
        raise QuadraticHyperbolicityError("companion state is not 128")
    if checks["eigenvector_deficit_each_root"] != 14:
        raise QuadraticHyperbolicityError(
            "unexpected companion eigenvector deficit"
        )

    chain_map = map_all_chains(packet)
    growth = growth_ledger()
    return {
        "schema_id": (
            "CALC_QFT_GR_QUADRATIC_FROZEN_COEFFICIENT_JORDAN_CHAIN_"
            "FREQUENCY_GROWTH_v0"
        ),
        "calculation_id": (
            "CALC-QFT-GR-QUADRATIC-FROZEN-COEFFICIENT-JORDAN-CHAIN-"
            "FREQUENCY-GROWTH-v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "execution_target": CURRENT_TARGET,
        "consumed_authority": {
            "path": ENERGY_REVIEW_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(ENERGY_REVIEW_PATH),
            "accepted_results": review["accepted_results"],
        },
        "consumed_energy_hierarchy": {
            "path": ENERGY_PACKET_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(ENERGY_PACKET_PATH),
            "prepared_chain_partition": "4J_3+6J_2+40J_1",
            "prepared_loss_candidates": [1, 2],
        },
        "frozen_background_contract": {
            "generic_admissible_jet": (
                "A pointwise frozen jet of the exact zero-constraint-"
                "addition vacuum reduced equations, in a local orthonormal "
                "frame, with Lorentzian metric, prescribed C^2 H(x,g), and "
                "all displayed coefficient matrices bounded by a declared "
                "finite constant B."
            ),
            "constraint_satisfying_background": (
                "The same frozen class with every accepted gauge, "
                "definition, trace, divergence, integrability, Hamiltonian, "
                "and momentum background constraint set to zero."
            ),
            "controls": [
                "Minkowski with c_Lambda=0, H=0, R=r=S=c=0",
                (
                    "constant-curvature Einstein background with "
                    "r=0 and trace-free Ricci S=0"
                ),
                "2alpha+beta=0 internal rank control",
            ],
            "coefficient_domain": [
                "beta != 0",
                "gamma:=3alpha+beta != 0",
            ],
            "uniformity_boundary": (
                "Bounds are uniform for fixed positive distance from "
                "beta=0 and gamma=0, fixed B, both roots, and every "
                "normalized nonzero spatial direction. They are not "
                "uniform as an excluded coefficient surface is approached "
                "or B is allowed to diverge."
            ),
        },
        "exact_companion": {
            "ordering": (
                "X=(rho W U,W partial_t U), "
                "U=(g[10],c[40],R[1],r[4],S[9])"
            ),
            "dimension": 128,
            "chain_block_formula": (
                "A_m(rho)=[[0,rho I_m],"
                "[-rho(I_m-N_m),0]]"
            ),
            "root_modal_formula": (
                "A_(m,lambda)^ME=i lambda rho I_m+rho N_m; "
                "A_(m,lambda)^A=i lambda rho I_m+N_m"
            ),
            "partition_checks": checks,
            "all_chain_mapping": chain_map,
        },
        "frequency_growth": growth,
        "sector_results": {
            "equal_order_auxiliary": {
                "minimum_frozen_loss": 0,
                "upper_bound_established": True,
                "saturating_lower_bound_established": True,
                "outcome": "FROZEN_AUXILIARY_ZERO_LOSS_CONFIRMED",
            },
            "adapted_auxiliary": {
                "minimum_frozen_loss": 0,
                "upper_bound_established": True,
                "saturating_lower_bound_established": True,
                "outcome": "FROZEN_AUXILIARY_ZERO_LOSS_CONFIRMED",
            },
            "unrestricted_metric_equivalence": {
                "pure_principal_minimum_loss_when_2alpha_plus_beta_nonzero": 2,
                "pure_principal_minimum_loss_on_2alpha_plus_beta_zero_control": 1,
                "complete_generic_frozen_minimum_loss": "BLOCKED",
                "length_three_saturating_chain_count": 4,
                "length_two_saturating_chain_count": 6,
                "pure_principal_upper_bound_established": True,
                "pure_principal_saturating_lower_bound_established": True,
                "complete_operator_upper_bound_established": False,
                "complete_operator_lower_bound_established": False,
                "outcome": (
                    "PURE_PRINCIPAL_METRIC_EQUIVALENCE_TWO_DERIVATIVE_"
                    "GROWTH_COMPLETE_GENERIC_FROZEN_LOSS_BLOCKED"
                ),
            },
            "physical_TT": {
                "pure_principal_minimum_loss": 1,
                "complete_generic_frozen_minimum_loss": "BLOCKED",
                "polarization_count": 2,
                "chain_length": 2,
                "pure_principal_upper_bound_established": True,
                "pure_principal_saturating_lower_bound_established": True,
                "complete_operator_upper_bound_established": False,
                "complete_operator_lower_bound_established": False,
                "outcome": (
                    "PURE_PRINCIPAL_PHYSICAL_TT_ONE_DERIVATIVE_GROWTH_"
                    "COMPLETE_GENERIC_FROZEN_LOSS_BLOCKED"
                ),
            },
            "semisimple": {
                "minimum_frozen_loss": 0,
                "chain_count": 40,
                "upper_bound_established": True,
                "saturating_lower_bound_established": True,
            },
            "constraint_compatible": {
                "minimum_frozen_loss": "BLOCKED",
                "proved_bounds": [1, 2],
                "TT_lower_bound": 1,
                "unrestricted_upper_bound": 2,
                "blocking_input": (
                    "The predecessor supplies the 69-component subsidiary "
                    "symbol and qualitative chain constraint labels, but "
                    "not a single explicit 128-state tangent projector "
                    "intertwining both companion roots and all definition, "
                    "curvature, gauge, Hamiltonian, and momentum constraints."
                ),
                "why_no_inference": (
                    "C_r and C_c can pair reconstruction variables and may "
                    "reduce the effective J_3 contribution. Strong "
                    "hyperbolicity of the subsidiary system alone does not "
                    "decide the restricted propagator minimum."
                ),
                "outcome": (
                    "CONSTRAINT_RESTRICTED_LOSS_BLOCKED_BY_MISSING_"
                    "TANGENT_PROJECTOR"
                ),
            },
        },
        "separate_loss_maps": {
            "r_in": {
                "value": "NOT_COMPOSED_IN_THIS_CALCULATION",
                "reason": (
                    "The accepted one-derivative equivalence shift is a "
                    "data/reconstruction-map statement, not evolution."
                ),
            },
            "r_prop": {
                "auxiliary": 0,
                "unrestricted_metric_equivalence": (
                    "PURE_PRINCIPAL_2_COMPLETE_GENERIC_FROZEN_BLOCKED"
                ),
                "physical_TT": (
                    "PURE_PRINCIPAL_1_COMPLETE_GENERIC_FROZEN_BLOCKED"
                ),
                "constraint_compatible": "BLOCKED_BETWEEN_1_AND_2",
            },
            "r_out": {
                "value": "NOT_COMPOSED_IN_THIS_CALCULATION",
                "reason": (
                    "No independent input/output map factorization with a "
                    "bounded inverse was established."
                ),
            },
            "known_equivalence_map_shift": 1,
            "total_metric_loss_summed": False,
        },
        "terminal_outcomes": [
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
        ],
        "claim_boundary": {
            "exact_128_component_companion_ordering_frozen": True,
            "all_fifty_chains_each_root_mapped": True,
            "pure_chain_fourier_exponentials_computed": True,
            "block_level_weighted_order_graph_screened": True,
            "positive_subprincipal_return_cycle_found": False,
            "complete_generic_frozen_operator_constructed": False,
            "finite_frozen_loss_for_bounded_background_class": False,
            "pure_principal_unrestricted_minimum_loss_established": True,
            "pure_principal_physical_TT_minimum_loss_established": True,
            "complete_generic_unrestricted_minimum_loss_established": False,
            "complete_generic_physical_TT_minimum_loss_established": False,
            "constraint_tangent_projector_constructed": False,
            "constraint_restricted_minimum_loss_established": False,
            "variable_coefficient_energy_estimate_established": False,
            "quasilinear_tame_estimate_established": False,
            "loss_nonaccumulation_established": False,
            "local_existence_established": False,
            "uniqueness_established": False,
            "continuous_dependence_established": False,
        },
        "prohibitions_respected": {
            "equivalence_shift_called_propagator_loss": False,
            "constraint_restricted_loss_inferred_without_projector": False,
            "principal_matrix_alone_called_variable_coefficient_estimate": False,
            "order_reduction_presented_as_original_theory": False,
            "regularizer_or_fiducial_mode_added": False,
            "source_extension_executed": False,
            "ghost_analysis_executed": False,
            "phenomenology_executed": False,
            "yukawa_work_executed": False,
        },
        "selected_next_target": RESULT_REVIEW_TARGET,
        "verdict": (
            "FROZEN_AUXILIARY_ZERO_LOSS_PURE_PRINCIPAL_METRIC_TWO_"
            "DERIVATIVE_AND_TT_ONE_DERIVATIVE_GROWTH_COMPLETE_GENERIC_"
            "FROZEN_LOSS_BLOCKED_PENDING_EXACT_SUBPRINCIPAL_MATRIX_"
            "AND_CONSTRAINT_TANGENT_PROJECTOR_NO_VARIABLE_OR_NONLINEAR_"
            "CLAIM"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_calculation,
        description=(
            "quadratic-gravity frozen-coefficient Jordan-chain "
            "frequency-growth calculation"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
