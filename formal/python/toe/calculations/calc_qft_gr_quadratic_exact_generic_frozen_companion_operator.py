from __future__ import annotations

from typing import Iterable

import sympy as sp

from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    CAPTURED_AT_UTC,
    REPO_ROOT,
    QuadraticHyperbolicityError,
    canonical_json_bytes,
    read_json,
    sha256_bytes,
    sha256_path,
    write_or_check,
)


FREQUENCY_REVIEW_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_FROZEN_COEFFICIENT_JORDAN_CHAIN_FREQUENCY_"
    "GROWTH_RESULT_REVIEW_20260728_v0.json"
)
REDUCED_SYSTEM_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-QFT-GR-QUADRATIC-AUXILIARY-HARMONIC-REDUCED-SYSTEM-v0.json"
)
CONSTRAINT_SYSTEM_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-QFT-GR-QUADRATIC-GAUGE-AUXILIARY-CONSTRAINT-"
    "PROPAGATION-SYSTEM-v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-QFT-GR-QUADRATIC-EXACT-GENERIC-FROZEN-COMPANION-"
    "OPERATOR-v0.json"
)
CURRENT_TARGET = (
    "derive_qft_gr_quadratic_exact_generic_frozen_"
    "companion_operator_v0"
)
RESULT_REVIEW_TARGET = (
    "review_qft_gr_quadratic_exact_generic_frozen_"
    "companion_operator_v0_result"
)

SYMMETRIC_PAIRS = (
    (0, 0),
    (0, 1),
    (0, 2),
    (0, 3),
    (1, 1),
    (1, 2),
    (1, 3),
    (2, 2),
    (2, 3),
    (3, 3),
)
TRACEFREE_PAIRS = SYMMETRIC_PAIRS[:-1]
G_START = 0
C_START = 10
R_INDEX = 50
R_DERIVATIVE_START = 51
S_START = 55
REDUCED_DIMENSION = 64
COMPANION_DIMENSION = 128


def tracefree_inclusion_and_half_metric() -> tuple[sp.Matrix, sp.Matrix]:
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


def add_coordinate_derivative(
    *,
    position_matrix: sp.MutableSparseMatrix,
    velocity_matrix: sp.MutableSparseMatrix,
    row: int,
    column: int,
    derivative_index: int,
    coefficient: sp.Expr,
    spatial_covector: tuple[sp.Symbol, sp.Symbol, sp.Symbol],
) -> None:
    if derivative_index == 0:
        velocity_matrix[row, column] += coefficient
        return
    position_matrix[row, column] += (
        sp.I * spatial_covector[derivative_index - 1] * coefficient
    )


def minkowski_control_rhs_matrices() -> dict[str, object]:
    """Construct F_U and F_V for W U = F on the exact flat control.

    The control fixes eta=(-,+,+,+), c=R=r=S=0, all background field
    derivatives to zero, H identically zero, and c_Lambda=0.  The remaining
    symbolic parameters are the three spatial Fourier components and the
    exact combinations m_R=c_R/[2(3 alpha+beta)],
    m_S=c_R/beta, and a=(2 alpha+beta)/beta.
    """

    k1, k2, k3 = sp.symbols("k1 k2 k3", real=True)
    m_r, m_s, a = sp.symbols("m_R m_S a", real=True)
    spatial_covector = (k1, k2, k3)
    position = sp.MutableSparseMatrix(
        REDUCED_DIMENSION, REDUCED_DIMENSION, {}
    )
    velocity = sp.MutableSparseMatrix(
        REDUCED_DIMENSION, REDUCED_DIMENSION, {}
    )
    inclusion, half_metric = tracefree_inclusion_and_half_metric()

    # F_g = -u R - 2 J S.
    for metric_component in range(10):
        position[G_START + metric_component, R_INDEX] += (
            -half_metric[metric_component, 0]
        )
        for spin_component in range(9):
            position[
                G_START + metric_component,
                S_START + spin_component,
            ] += -2 * inclusion[metric_component, spin_component]

    # F_R = m_R R.
    position[R_INDEX, R_INDEX] += m_r

    # F_r_a = m_R partial_a R.
    for derivative_index in range(4):
        add_coordinate_derivative(
            position_matrix=position,
            velocity_matrix=velocity,
            row=R_DERIVATIVE_START + derivative_index,
            column=R_INDEX,
            derivative_index=derivative_index,
            coefficient=m_r,
            spatial_covector=spatial_covector,
        )

    # F_c_mna = -u_mn partial_a R -2 J_mn^A partial_a S_A.
    for derivative_index in range(4):
        for metric_component in range(10):
            row = C_START + 10 * derivative_index + metric_component
            add_coordinate_derivative(
                position_matrix=position,
                velocity_matrix=velocity,
                row=row,
                column=R_INDEX,
                derivative_index=derivative_index,
                coefficient=-half_metric[metric_component, 0],
                spatial_covector=spatial_covector,
            )
            for spin_component in range(9):
                coefficient = -2 * inclusion[
                    metric_component, spin_component
                ]
                if coefficient == 0:
                    continue
                add_coordinate_derivative(
                    position_matrix=position,
                    velocity_matrix=velocity,
                    row=row,
                    column=S_START + spin_component,
                    derivative_index=derivative_index,
                    coefficient=coefficient,
                    spatial_covector=spatial_covector,
                )

    # F_S_mn = a[partial_m r_n -(eta_mn/4)m_R R] -m_S S_mn.
    eta_diagonal = (-1, 1, 1, 1)
    for spin_component, (m_index, n_index) in enumerate(
        TRACEFREE_PAIRS
    ):
        row = S_START + spin_component
        add_coordinate_derivative(
            position_matrix=position,
            velocity_matrix=velocity,
            row=row,
            column=R_DERIVATIVE_START + n_index,
            derivative_index=m_index,
            coefficient=a,
            spatial_covector=spatial_covector,
        )
        if m_index == n_index:
            position[row, R_INDEX] += (
                -a * sp.Rational(1, 4) * eta_diagonal[m_index] * m_r
            )
        position[row, S_START + spin_component] += -m_s

    return {
        "position": position,
        "velocity": velocity,
        "symbols": {
            "k1": k1,
            "k2": k2,
            "k3": k3,
            "m_R": m_r,
            "m_S": m_s,
            "a": a,
        },
    }


def minkowski_control_companion() -> sp.MutableSparseMatrix:
    rhs = minkowski_control_rhs_matrices()
    position = rhs["position"]
    velocity = rhs["velocity"]
    if not isinstance(position, sp.MutableSparseMatrix) or not isinstance(
        velocity, sp.MutableSparseMatrix
    ):
        raise QuadraticHyperbolicityError("unexpected RHS matrix type")
    symbols = rhs["symbols"]
    if not isinstance(symbols, dict):
        raise QuadraticHyperbolicityError("unexpected symbol map")
    rho_squared = (
        symbols["k1"] ** 2
        + symbols["k2"] ** 2
        + symbols["k3"] ** 2
    )
    companion = sp.MutableSparseMatrix(
        COMPANION_DIMENSION, COMPANION_DIMENSION, {}
    )
    for component in range(REDUCED_DIMENSION):
        companion[component, REDUCED_DIMENSION + component] = 1
        companion[
            REDUCED_DIMENSION + component, component
        ] = -rho_squared
    for (row, column), value in position.todok().items():
        companion[
            REDUCED_DIMENSION + row, column
        ] -= value
    for (row, column), value in velocity.todok().items():
        companion[
            REDUCED_DIMENSION + row,
            REDUCED_DIMENSION + column,
        ] -= value
    return companion


def sparse_entry_ledger(
    matrix: sp.MutableSparseMatrix,
) -> list[dict[str, int | str]]:
    entries: list[dict[str, int | str]] = []
    for (row, column), value in sorted(matrix.todok().items()):
        simplified = sp.factor(value)
        if simplified == 0:
            continue
        entries.append(
            {
                "row": row,
                "column": column,
                "value": sp.sstr(simplified),
            }
        )
    return entries


def contains_any(value: str, tokens: Iterable[str]) -> bool:
    return any(token in value for token in tokens)


def generic_closure_audit(reduced: dict, constraint: dict) -> dict:
    exact_definitions = reduced["exact_operator_definitions"]
    closed_system = reduced["closed_second_order_system"]
    serialized = canonical_json_bytes(
        {
            "exact_operator_definitions": exact_definitions,
            "closed_second_order_system": closed_system,
        }
    ).decode("utf-8")
    unresolved_tokens = [
        token
        for token in (
            "Q^H_mn",
            "Q_mn(g,c)",
            "L^S_mn",
            "partial_a F^R",
            "partial_a F^g_mn",
        )
        if token in serialized
    ]
    if len(unresolved_tokens) != 5:
        raise QuadraticHyperbolicityError(
            "the expected component-expansion blockers changed"
        )
    constraint_extension = constraint["off_constraint_extension"]
    return {
        "target_question": (
            "Can every entry of the generic background-dependent 128 by "
            "128 frozen companion be generated from accepted predecessor "
            "artifacts without an unnamed remainder or unbound jet?"
        ),
        "answer": False,
        "terminal_outcome": "GENERIC_BACKGROUND_OPERATOR_NOT_YET_CLOSED",
        "blocking_placeholders_found_in_predecessor": unresolved_tokens,
        "off_constraint_extension": {
            "status": "FROZEN",
            "constraint_addition_M_A_B": constraint_extension[
                "constraint_addition_M_A_B"
            ],
            "derivative_constraint_addition_N_A_B_mu": (
                constraint_extension[
                    "derivative_constraint_addition_N_A_B_mu"
                ]
            ),
            "blocking": False,
        },
        "closure_requirements": [
            {
                "id": "EXACT_REDUCED_VARIABLE_ORDER",
                "status": "PASS",
                "evidence": "U=(g[10],c[40],R[1],r[4],S[9])",
            },
            {
                "id": "ZERO_ADDITION_OFF_CONSTRAINT_EXTENSION",
                "status": "PASS",
                "evidence": (
                    "The accepted subsidiary packet freezes the literal "
                    "zero-constraint-addition reduced equations."
                ),
            },
            {
                "id": "QH_COMPONENT_EXPANSION",
                "status": "BLOCKED",
                "evidence": (
                    "Q_mn and Q^H_mn remain named remainders rather than "
                    "component polynomials in g,c and the prescribed H jet."
                ),
            },
            {
                "id": "TENSOR_BOX_REMAINDER_COMPONENT_EXPANSION",
                "status": "BLOCKED",
                "evidence": (
                    "L^S_mn remains a named tensor-box remainder rather "
                    "than a component polynomial in g,c,partial c,S,"
                    "partial S."
                ),
            },
            {
                "id": "DERIVATIVE_EQUATION_EXPANSION",
                "status": "BLOCKED",
                "evidence": (
                    "F_r and F_c still use partial_a F^R and "
                    "partial_a F^g; their component Jacobians are absent."
                ),
            },
            {
                "id": "PRESCRIBED_GAUGE_SOURCE_JET",
                "status": "BLOCKED",
                "evidence": (
                    "H(x,g) is specified only as prescribed C^2. Its "
                    "independent H_x,H_g,H_xx,H_xg,H_gg jet coordinates "
                    "and admissibility identities are not frozen."
                ),
            },
            {
                "id": "INDEPENDENT_ON_SHELL_BACKGROUND_JET",
                "status": "BLOCKED",
                "evidence": (
                    "No nonredundant coordinate set for "
                    "(Ubar,partial Ubar,partial^2 Ubar,Weylbar) modulo "
                    "field equations, gauge, and definition constraints "
                    "has been selected."
                ),
            },
            {
                "id": "GENERIC_128_STATE_COEFFICIENT_JACOBIANS",
                "status": "BLOCKED",
                "evidence": (
                    "The exact dF/dU and dF/d(partial_a U) matrices and "
                    "the coefficient-variation terms "
                    "delta(g^ab) partial_a partial_b Ubar do not exist "
                    "as accepted artifacts."
                ),
            },
            {
                "id": "FULL_CONSTRAINT_TANGENT_PROJECTOR",
                "status": "DEFERRED_NOT_REQUIRED_FOR_UNRESTRICTED_OPERATOR",
                "evidence": (
                    "Still required before a constraint-restricted "
                    "spectral minimum can be calculated."
                ),
            },
        ],
        "required_background_contract_for_successor": {
            "class": (
                "vacuum on-shell, full-constraint-satisfying generic "
                "background two-jet in a foliation-adapted orthonormal "
                "frame at the frozen point"
            ),
            "must_name_independent_coordinates": [
                "Ubar=(gbar,cbar,Rbar,rbar,Sbar)",
                "partial Ubar",
                "independent second derivatives of Ubar",
                "background Weyl components not fixed by Rbar,Sbar",
                "H_x,H_g,H_xx,H_xg,H_gg at (xbar,gbar)",
            ],
            "must_record_relations": [
                "background reduced evolution equations",
                "harmonic gauge and all auxiliary definition constraints",
                "trace and divergence constraints",
                "integrability constraints",
                "Hamiltonian and momentum constraints",
            ],
            "controls_not_generic": [
                "Minkowski",
                "constant-curvature Einstein",
                "2alpha+beta=0",
            ],
        },
        "why_order_graph_is_insufficient": (
            "A block-level differential-order graph records possible "
            "frequency powers but not the coefficient products around "
            "Jordan return paths. It cannot decide cancellations, "
            "fractional root splitting, real parts, or background and "
            "direction uniformity."
        ),
    }


def build_calculation() -> dict:
    authority = read_json(FREQUENCY_REVIEW_PATH)
    reduced = read_json(REDUCED_SYSTEM_PATH)
    constraint = read_json(CONSTRAINT_SYSTEM_PATH)
    if authority["accepted"] is not True:
        raise QuadraticHyperbolicityError(
            "frozen-frequency result review was not accepted"
        )
    if authority["selected_next_target"] != CURRENT_TARGET:
        raise QuadraticHyperbolicityError(
            "exact generic frozen companion authority mismatch"
        )
    if authority["authority_rotation"][
        "exact_generic_frozen_companion_operator_authorized"
    ] is not True:
        raise QuadraticHyperbolicityError(
            "generic frozen companion execution is not authorized"
        )

    companion = minkowski_control_companion()
    entries = sparse_entry_ledger(companion)
    forbidden = ("O(", "lower", "remainder", "Q^H", "L^S")
    if companion.shape != (128, 128):
        raise QuadraticHyperbolicityError(
            "Minkowski companion has the wrong dimension"
        )
    if any(
        contains_any(str(row["value"]), forbidden) for row in entries
    ):
        raise QuadraticHyperbolicityError(
            "Minkowski matrix contains an implicit remainder"
        )
    if sum(
        row["row"] < 64
        and row["column"] == 64 + row["row"]
        and row["value"] == "1"
        for row in entries
    ) != 64:
        raise QuadraticHyperbolicityError(
            "Minkowski companion top identity block is incomplete"
        )

    audit = generic_closure_audit(reduced, constraint)
    return {
        "schema_id": (
            "CALC_QFT_GR_QUADRATIC_EXACT_GENERIC_FROZEN_"
            "COMPANION_OPERATOR_v0"
        ),
        "calculation_id": (
            "CALC-QFT-GR-QUADRATIC-EXACT-GENERIC-FROZEN-"
            "COMPANION-OPERATOR-v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "execution_target": CURRENT_TARGET,
        "consumed_authority": {
            "path": FREQUENCY_REVIEW_PATH.relative_to(
                REPO_ROOT
            ).as_posix(),
            "sha256": sha256_path(FREQUENCY_REVIEW_PATH),
            "accepted_results": authority["accepted_results"],
        },
        "consumed_reduced_system": {
            "path": REDUCED_SYSTEM_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(REDUCED_SYSTEM_PATH),
        },
        "consumed_constraint_system": {
            "path": CONSTRAINT_SYSTEM_PATH.relative_to(
                REPO_ROOT
            ).as_posix(),
            "sha256": sha256_path(CONSTRAINT_SYSTEM_PATH),
        },
        "generic_operator_closure_audit": audit,
        "exact_minkowski_control": {
            "classification": (
                "MINKOWSKI_FROZEN_COMPANION_OPERATOR_EXACTLY_"
                "DERIVED_CONTROL_ONLY"
            ),
            "background_contract": {
                "metric": "eta=diag(-1,1,1,1)",
                "background_fields": "c=R=r=S=0",
                "background_field_derivatives": "all zero",
                "gauge_source": "H identically zero",
                "cosmological_coefficient": "c_Lambda=0",
                "coefficient_domain": [
                    "beta != 0",
                    "gamma:=3alpha+beta != 0",
                ],
                "not_generic": True,
            },
            "variable_order": [
                "g_mn[10]",
                "c_mna[40], derivative index a outermost",
                "R[1]",
                "r_a[4]",
                "S_mn[9], S_33=S_00-S_11-S_22",
                "partial_t of the preceding 64 variables",
            ],
            "parameter_definitions": {
                "rho_squared": "k1**2+k2**2+k3**2",
                "m_R": "c_R/[2(3alpha+beta)]",
                "m_S": "c_R/beta",
                "a": "(2alpha+beta)/beta",
            },
            "first_order_form": (
                "X=(U,V), partial_t X=A_Mink(k)X; "
                "A_Mink=[[0,I_64],[-rho^2 I_64-F_U,-F_V]]"
            ),
            "rhs_equations": [
                "F_g_mn=-(1/2)eta_mn R-2S_mn",
                "F_R=m_R R",
                "F_r_a=m_R partial_a R",
                (
                    "F_c_mna=-(1/2)eta_mn partial_a R"
                    "-2 partial_a S_mn"
                ),
                (
                    "F_S_mn=a[partial_m r_n"
                    "-(1/4)eta_mn m_R R]-m_S S_mn"
                ),
            ],
            "matrix_shape": list(companion.shape),
            "nonzero_entry_count": len(entries),
            "sparse_entries": entries,
            "sparse_entry_sha256": sha256_bytes(
                canonical_json_bytes(entries)
            ),
            "placeholder_free": True,
            "generic_background_conclusion": False,
        },
        "terminal_outcomes": [
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
        ],
        "claim_boundary": {
            "exact_minkowski_control_operator_derived": True,
            "exact_generic_background_operator_derived": False,
            "generic_characteristic_asymptotics_derived": False,
            "generic_finite_loss_established": False,
            "generic_fractional_root_splitting_excluded": False,
            "constraint_tangent_projector_constructed": False,
            "constraint_restricted_minimum_loss_established": False,
            "variable_coefficient_estimate_established": False,
            "quasilinear_estimate_established": False,
            "local_well_posedness_established": False,
        },
        "prohibitions_respected": {
            "named_remainder_inserted_as_exact_matrix_entry": False,
            "minkowski_control_called_generic": False,
            "order_graph_called_spectral_proof": False,
            "constraint_projection_inferred": False,
            "variable_coefficient_estimate_claimed": False,
            "quasilinear_or_local_theorem_claimed": False,
            "source_extension_executed": False,
            "ghost_analysis_executed": False,
            "phenomenology_executed": False,
            "yukawa_work_executed": False,
        },
        "selected_next_target": RESULT_REVIEW_TARGET,
        "verdict": (
            "EXACT_MINKOWSKI_COMPANION_CONTROL_DERIVED_GENERIC_"
            "BACKGROUND_OPERATOR_NOT_CLOSED_PENDING_COMPONENT_EXPANSION_"
            "GAUGE_JET_AND_ON_SHELL_BACKGROUND_JET_NO_GENERIC_SPECTRAL_"
            "VARIABLE_OR_NONLINEAR_CLAIM"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_calculation,
        description=(
            "quadratic-gravity exact generic frozen companion "
            "operator closure calculation"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
