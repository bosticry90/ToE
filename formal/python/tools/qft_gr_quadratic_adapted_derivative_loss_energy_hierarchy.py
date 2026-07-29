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


PRINCIPAL_REVIEW_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_FULL_REDUCED_SYSTEM_PRINCIPAL_STRUCTURE_"
    "RESULT_REVIEW_20260728_v0.json"
)
PRINCIPAL_CALCULATION_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-QFT-GR-QUADRATIC-FULL-REDUCED-SYSTEM-PRINCIPAL-"
    "STRUCTURE-v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_ADAPTED_DERIVATIVE_LOSS_ENERGY_"
    "HIERARCHY_20260728_v0.json"
)
CURRENT_TARGET = (
    "prepare_qft_gr_quadratic_adapted_derivative_loss_"
    "energy_hierarchy_v0"
)
REVIEW_TARGET = (
    "review_qft_gr_quadratic_adapted_derivative_loss_"
    "energy_hierarchy_v0_result"
)
EXECUTION_TARGET = (
    "compute_qft_gr_quadratic_frozen_coefficient_"
    "jordan_chain_frequency_growth_v0"
)

S_COMPONENTS = (
    "S_00",
    "S_01",
    "S_02",
    "S_03",
    "S_11",
    "S_12",
    "S_13",
    "S_22",
    "S_23",
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


def _tracefree_hessian_map(lam: int) -> sp.Matrix:
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


def _linear_combination(vector: sp.Matrix, names: tuple[str, ...]) -> str:
    terms: list[str] = []
    for coefficient, name in zip(vector, names, strict=True):
        if coefficient == 0:
            continue
        terms.append(f"({sp.sstr(coefficient)}){name}")
    return " + ".join(terms) if terms else "0"


def _curvature_complement() -> list[dict]:
    tt_plus = sp.Matrix([-1, 0, 0, 0, 1, 0, 0, 2, 0])
    tt_cross = sp.eye(9)[:, 8]
    return [
        {
            "id": "R_scalar",
            "vector": None,
            "top_variable": "R",
            "leading_mode": "AUXILIARY_SCALAR_CURVATURE",
            "constraint_status": (
                "UNRESOLVED_REQUIRES_EXACT_CONSTRAINT_TANGENT_PROJECTION"
            ),
        },
        {
            "id": "S_TT_plus",
            "vector": tt_plus,
            "top_variable": "-S_00+S_11+2S_22 (=S_22-S_33)",
            "leading_mode": "PHYSICAL_SPIN2_TT_PLUS",
            "constraint_status": (
                "TANGENT_TO_PHYSICAL_CONSTRAINT_SURFACE_IN_TT_SECTOR"
            ),
        },
        {
            "id": "S_TT_cross",
            "vector": tt_cross,
            "top_variable": "S_23",
            "leading_mode": "PHYSICAL_SPIN2_TT_CROSS",
            "constraint_status": (
                "TANGENT_TO_PHYSICAL_CONSTRAINT_SURFACE_IN_TT_SECTOR"
            ),
        },
        {
            "id": "S_aux_00",
            "vector": sp.eye(9)[:, 0],
            "top_variable": "S_00",
            "leading_mode": "NON_TT_AUXILIARY_CURVATURE_QUOTIENT",
            "constraint_status": (
                "UNRESOLVED_REQUIRES_EXACT_CONSTRAINT_TANGENT_PROJECTION"
            ),
        },
        {
            "id": "S_aux_02",
            "vector": sp.eye(9)[:, 2],
            "top_variable": "S_02",
            "leading_mode": "NON_TT_AUXILIARY_CURVATURE_QUOTIENT",
            "constraint_status": (
                "UNRESOLVED_REQUIRES_EXACT_CONSTRAINT_TANGENT_PROJECTION"
            ),
        },
        {
            "id": "S_aux_03",
            "vector": sp.eye(9)[:, 3],
            "top_variable": "S_03",
            "leading_mode": "NON_TT_AUXILIARY_CURVATURE_QUOTIENT",
            "constraint_status": (
                "UNRESOLVED_REQUIRES_EXACT_CONSTRAINT_TANGENT_PROJECTION"
            ),
        },
    ]


def build_jordan_chain_ledger() -> dict:
    """Build all fifty chains at each light-cone root."""
    roots: dict[str, list[dict]] = {}
    rank_checks: dict[str, dict] = {}
    complement = _curvature_complement()
    for lam in (-1, 1):
        hessian = _tracefree_hessian_map(lam)
        s_complement = sp.Matrix.hstack(
            hessian,
            *[
                row["vector"]
                for row in complement
                if row["vector"] is not None
            ],
        )
        rows: list[dict] = []
        for index in range(4):
            middle = _linear_combination(hessian[:, index], S_COMPONENTS)
            rows.append(
                {
                    "chain_id": f"lambda_{lam}_L3_r_{index}",
                    "root": lam,
                    "chain_length": 3,
                    "chain_variables": [
                        f"r_{index}",
                        f"H_{lam}(r_{index})={middle}",
                        (
                            "B[H(r)] in (g,c): "
                            "(2J H(r),2i ell tensor J H(r))"
                        ),
                    ],
                    "leading_mode": "AUXILIARY_DEFINITION_RECONSTRUCTION",
                    "raw_differential_maps": [
                        "r -> S: order 1 through H(ell)",
                        "S -> g: order 0; S -> c: order 1",
                    ],
                    "metric_weighted_orders": [2, 2],
                    "conventional_first_order_frequency_growth": (
                        "1+|k|t+(|k|t)^2/2"
                    ),
                    "raw_growth_exponent": 2,
                    "weight_absorption": (
                        "The adapted grading can absorb one displayed "
                        "frequency power, but the exact companion propagator "
                        "must decide whether a residual power remains."
                    ),
                    "net_loss": "UNRESOLVED_ONE_OR_TWO_DERIVATIVES",
                    "constraint_status": (
                        "TRANSVERSE_AS_ISOLATED_CHAIN; constraint-compatible "
                        "only after C_r,C_S,C_c are imposed"
                    ),
                }
            )
        for item in complement:
            physical = item["leading_mode"].startswith("PHYSICAL_SPIN2")
            rows.append(
                {
                    "chain_id": f"lambda_{lam}_L2_{item['id']}",
                    "root": lam,
                    "chain_length": 2,
                    "chain_variables": [
                        item["top_variable"],
                        (
                            "B[z] in (g,c): "
                            "(uR+2JS,i ell tensor (uR+2JS))"
                        ),
                    ],
                    "leading_mode": item["leading_mode"],
                    "raw_differential_maps": [
                        "R or S -> g: order 0",
                        "R or S -> c: order 1",
                    ],
                    "metric_weighted_orders": [2, 2],
                    "conventional_first_order_frequency_growth": "1+|k|t",
                    "raw_growth_exponent": 1,
                    "weight_absorption": (
                        "Physical TT reconstruction is the q^2 metric "
                        "block; the exact companion propagator must determine "
                        "whether the adapted shift absorbs its one power."
                        if physical
                        else (
                            "The curvature-to-(g,c) grading supplies one "
                            "candidate shift; constraint projection and the "
                            "exact companion propagator remain required."
                        )
                    ),
                    "net_loss": (
                        "UNRESOLVED_ZERO_OR_ONE_DERIVATIVE"
                        if physical
                        else "UNRESOLVED_ZERO_OR_ONE_DERIVATIVE"
                    ),
                    "constraint_status": item["constraint_status"],
                }
            )
        for derivative_index in range(4):
            for pair in SYMMETRIC_COMPONENTS:
                rows.append(
                    {
                        "chain_id": (
                            f"lambda_{lam}_L1_c_{pair}_{derivative_index}"
                        ),
                        "root": lam,
                        "chain_length": 1,
                        "chain_variables": [
                            f"c_{pair},{derivative_index} complement vector"
                        ],
                        "leading_mode": "METRIC_DEFINITION_SEMISIMPLE",
                        "raw_differential_maps": [],
                        "metric_weighted_orders": [],
                        "conventional_first_order_frequency_growth": "1",
                        "raw_growth_exponent": 0,
                        "weight_absorption": "none required",
                        "net_loss": 0,
                        "constraint_status": (
                            "TRANSVERSE_TO_C_c=0 AS_ISOLATED_VECTOR; "
                            "constraint-compatible only when paired with g"
                        ),
                    }
                )
        roots[str(lam)] = rows
        rank_checks[str(lam)] = {
            "H_rank": hessian.rank(),
            "H_plus_selected_S_complement_rank": s_complement.rank(),
            "selected_S_complement": [
                item["id"] for item in complement if item["vector"] is not None
            ],
            "chain_count": len(rows),
            "length_3_count": sum(row["chain_length"] == 3 for row in rows),
            "length_2_count": sum(row["chain_length"] == 2 for row in rows),
            "length_1_count": sum(row["chain_length"] == 1 for row in rows),
            "algebraic_dimension": sum(
                row["chain_length"] for row in rows
            ),
            "geometric_dimension": len(rows),
            "eigenvector_deficit": sum(
                row["chain_length"] - 1 for row in rows
            ),
            "physical_deficit": sum(
                row["chain_length"] - 1
                for row in rows
                if row["leading_mode"].startswith("PHYSICAL_SPIN2")
            ),
        }
    return {
        "basis_frame": (
            "khat=e_1 with transverse directions e_2,e_3; other directions "
            "follow by the frozen spatial rotational covariance already "
            "accepted in the principal-structure review"
        ),
        "tracefree_completion": "S_33=S_00-S_11-S_22",
        "roots": roots,
        "rank_and_count_checks": rank_checks,
        "deficit_decomposition_each_root": {
            "total_missing_eigenvectors": 14,
            "physical_TT_size_2_chains": 2,
            "missing_from_physical_TT": 2,
            "size_3_reconstruction_chains": 4,
            "missing_from_size_3_reconstruction": 8,
            "non_TT_size_2_chains": 4,
            "missing_from_non_TT_size_2": 4,
            "check": "2+8+4=14",
        },
        "claim_boundary": (
            "The chain ledger and raw Jordan growth ceilings are exact. "
            "They do not identify the frozen companion generator or prove "
            "that the adapted net propagator loss is one derivative."
        ),
    }


def build_packet() -> dict:
    principal_review = read_json(PRINCIPAL_REVIEW_PATH)
    principal = read_json(PRINCIPAL_CALCULATION_PATH)
    if principal_review["accepted"] is not True:
        raise QuadraticHyperbolicityError(
            "principal-structure result review was not accepted"
        )
    if principal_review["selected_next_target"] != CURRENT_TARGET:
        raise QuadraticHyperbolicityError(
            "adapted energy-hierarchy authority mismatch"
        )
    if principal["claim_boundary"]["energy_estimate_established"]:
        raise QuadraticHyperbolicityError(
            "predecessor already claims an energy estimate"
        )

    ledger = build_jordan_chain_ledger()
    for root in ("-1", "1"):
        check = ledger["rank_and_count_checks"][root]
        if check != {
            "H_rank": 4,
            "H_plus_selected_S_complement_rank": 9,
            "selected_S_complement": [
                "S_TT_plus",
                "S_TT_cross",
                "S_aux_00",
                "S_aux_02",
                "S_aux_03",
            ],
            "chain_count": 50,
            "length_3_count": 4,
            "length_2_count": 6,
            "length_1_count": 40,
            "algebraic_dimension": 64,
            "geometric_dimension": 50,
            "eigenvector_deficit": 14,
            "physical_deficit": 2,
        }:
            raise QuadraticHyperbolicityError(
                f"unexpected Jordan ledger at lambda={root}"
            )

    return {
        "schema_id": (
            "QFT_GR_QUADRATIC_ADAPTED_DERIVATIVE_LOSS_"
            "ENERGY_HIERARCHY_20260728_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "preparation_target": CURRENT_TARGET,
        "consumed_authority": {
            "path": PRINCIPAL_REVIEW_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(PRINCIPAL_REVIEW_PATH),
            "accepted_results": principal_review["accepted_results"],
        },
        "consumed_principal_structure": {
            "path": PRINCIPAL_CALCULATION_PATH.relative_to(
                REPO_ROOT
            ).as_posix(),
            "sha256": sha256_path(PRINCIPAL_CALCULATION_PATH),
            "adapted_auxiliary_pencil": "q I_64",
            "metric_jordan_partition": "4J_3+6J_2+40J_1",
            "equivalence_map_derivative_loss": 1,
        },
        "frozen_scope": {
            "theory": (
                "sqrt(-g)[c_R R+c_Lambda+alpha R^2+beta R_mn R^mn]"
            ),
            "source": "VACUUM",
            "dimension": 4,
            "metric_signature": "(-,+,+,+)",
            "gauge": "GENERALIZED_HARMONIC_WITH_PRESCRIBED_H(x,g)",
            "generic_sector": [
                "beta != 0",
                "gamma:=3alpha+beta != 0",
            ],
            "unknown_order": ["g_mn", "c_mna", "R", "r_a", "S_mn"],
            "no_new_physics_or_formulation": True,
        },
        "loss_distinction": {
            "proved_equivalence_map_shift": 1,
            "meaning": (
                "Identifying S in H^(s+1) with Ricci[g] requires g in "
                "H^(s+3), one derivative above the accepted H^(s+2) "
                "auxiliary baseline."
            ),
            "propagator_loss_candidate": [1, 2],
            "propagator_loss_established": False,
            "reason": (
                "A size-three root chain has a conventional raw quadratic "
                "frequency-growth ceiling. The second-order companion "
                "generator and derivative weights must be applied before "
                "the net loss can be reduced to one."
            ),
        },
        "jordan_chain_ledger": ledger,
        "energy_definitions": {
            "coercive_wave_energy": {
                "definition": (
                    "W_q[X;mu_X] := ||dt X||^2_H^q"
                    "+||grad X||^2_H^q+mu_X^2||X||^2_H^q"
                ),
                "reference_mass_weights": {
                    "g_mn": "mu_g^2=1",
                    "c_mna": "mu_c^2=1",
                    "r_a": "mu_r^2=1",
                    "R": "mu_R^2=1+|c_R/[2(3alpha+beta)]|",
                    "S_mn": "mu_S^2=1+|c_R/beta|",
                },
                "mass_note": (
                    "These positive reference weights make the norm "
                    "coercive; they do not assert a sign for a physical "
                    "mass or remove any lower-order coupling."
                ),
            },
            "equal_order_auxiliary": {
                "definition": (
                    "E_aux,s := sum_{X in (g,c,R,r,S)} W_s[X;mu_X]"
                ),
                "component_spatial_regularities": {
                    "g_mn": "H^(s+1)",
                    "c_mna": "H^(s+1)",
                    "R": "H^(s+1)",
                    "r_a": "H^(s+1)",
                    "S_mn": "H^(s+1)",
                },
                "candidate_estimate": (
                    "E_aux,s(t)<=C exp(Kt)[E_aux,s(0)"
                    "+integral_0^t ||F||^2_H^s]"
                ),
                "status": (
                    "PLAUSIBLE_FROM_FROZEN_AUXILIARY_SYMBOL_NOT_PROVED_"
                    "FOR_VARIABLE_COEFFICIENTS"
                ),
            },
            "natural_fourth_order_metric": {
                "definition": (
                    "E_metric,s := ||g||^2_H^(s+3)"
                    "+||dt g||^2_H^(s+2)"
                    "+||dt^2 g||^2_H^(s+1)"
                    "+||dt^3 g||^2_H^s"
                ),
                "same_order_generic_estimate": False,
                "reason": (
                    "The accepted physical q^2 I_2 block and the 64/50 "
                    "metric-equivalence multiplicities preclude a uniform "
                    "same-order estimate for arbitrary lower-order terms."
                ),
            },
            "adapted_auxiliary": {
                "definition": (
                    "E_A,s := W_(s+1)[g]+W_s[c]+W_(s+1)[R]"
                    "+W_s[r]+W_s[S]"
                ),
                "spatial_weights_sigma": {
                    "g_mn": 2,
                    "c_mna": 1,
                    "R": 2,
                    "r_a": 1,
                    "S_mn": 1,
                },
                "time_weights_tau": {
                    "g_mn": 1,
                    "c_mna": 0,
                    "R": 1,
                    "r_a": 0,
                    "S_mn": 0,
                },
                "frozen_principal_status": "q I_64 WITH T_A=I_64",
                "variable_coefficient_estimate_proved": False,
            },
            "adapted_metric_equivalence": {
                "definition": (
                    "E_ME,s := W_(s+2)[g]+W_(s+1)[c]+W_s[R]"
                    "+W_(s-1)[r]+W_s[S]"
                ),
                "spatial_weights_sigma": {
                    "g_mn": 3,
                    "c_mna": 2,
                    "R": 1,
                    "r_a": 0,
                    "S_mn": 1,
                },
                "time_weights_tau": {
                    "g_mn": 2,
                    "c_mna": 1,
                    "R": 0,
                    "r_a": -1,
                    "S_mn": 0,
                },
                "weighted_principal_couplings": [
                    "E_g<-R,S",
                    "E_c<-partial R,partial S",
                    "E_S<-partial r",
                ],
                "status": (
                    "TRIANGULAR_CANDIDATE_REQUIRING_EXACT_FOURIER_"
                    "PROPAGATOR"
                ),
            },
            "constraint_compatible_total": {
                "definition": (
                    "E_total,s := E_A,s+kappa E_C,s, kappa>0"
                ),
                "constraint_vector": [
                    "C_H^a",
                    "Phi^a_b",
                    "V_H_n",
                    "C_r_a",
                    "C_c_mna",
                    "T",
                ],
                "independent_constraint_components": 69,
                "constraint_energy": (
                    "E_C,s := sum_A W_s[C_A;1]"
                ),
                "conditional_zero_preservation": (
                    "E_C,s(0)=0 implies E_C,s(t)=0 only conditional on "
                    "existence and uniqueness of a sufficiently regular "
                    "reduced solution."
                ),
                "physical_defect_repaired_by_constraint_energy": False,
            },
        },
        "weighted_lower_order_audit": {
            "terms_promoted_to_metric_weighted_principal_order": [
                {
                    "coupling": "E_g<-R,S",
                    "raw_order": 0,
                    "metric_weighted_order": 2,
                },
                {
                    "coupling": "E_c<-partial R,partial S",
                    "raw_order": 1,
                    "metric_weighted_order": 2,
                },
                {
                    "coupling": "E_S<-partial r",
                    "raw_order": 1,
                    "metric_weighted_order": 2,
                },
            ],
            "included_in_principal_matrix": True,
            "unlisted_promoted_term_found": False,
            "variable_coefficient_commutator_audit_executed": False,
            "classification": (
                "KNOWN_WEIGHTED_PRINCIPAL_CONTAMINATION_INCLUDED_"
                "NOT_YET_ESTIMATED"
            ),
        },
        "four_proof_levels": [
            {
                "level": 1,
                "id": "FROZEN_COEFFICIENT_FOURIER_PROPAGATOR",
                "required_construction": (
                    "Build the exact first-order-in-time companion A(k) for "
                    "all 64 variables and compute exp(t A(k))."
                ),
                "required_bound": (
                    "||exp(tA(k))||<=C_T(1+|k|)^r for 0<=t<=T"
                ),
                "decisions": [
                    "minimum integer r",
                    "r by Jordan-chain family",
                    "constraint-tangent versus transverse growth",
                    "one versus two derivative net loss",
                ],
                "status": "AUTHORIZED_NEXT_AFTER_ACCEPTED_REVIEW",
            },
            {
                "level": 2,
                "id": "VARIABLE_COEFFICIENT_LINEAR_ESTIMATE",
                "required_construction": (
                    "Prove uniform auxiliary symmetrizer positivity, bound "
                    "its derivatives and all commutators, and audit weighted "
                    "lower-order terms."
                ),
                "failure_trigger": (
                    "any uncontrolled term at or above weighted principal "
                    "order, or nonuniform symmetrizer bounds"
                ),
                "status": "NOT_AUTHORIZED_BY_THIS_PACKET",
            },
            {
                "level": 3,
                "id": "QUASILINEAR_TAME_ESTIMATE",
                "required_construction": (
                    "Separate a coefficient-controlling low norm s0 from "
                    "the differentiated high norm s and prove a tame bound."
                ),
                "failure_trigger": (
                    "high derivatives enter the coefficient factor "
                    "non-tamely or the loss grows with s"
                ),
                "status": "NOT_AUTHORIZED_BY_THIS_PACKET",
            },
            {
                "level": 4,
                "id": "ITERATION_CLOSURE",
                "required_construction": (
                    "Determine Picard closure, triangular nonaccumulation, "
                    "modified iteration, or a Nash-Moser requirement."
                ),
                "failure_trigger": (
                    "E_s[U_(n+1)] requires E_(s+1)[U_n] at every iteration"
                ),
                "status": "NOT_AUTHORIZED_BY_THIS_PACKET",
            },
        ],
        "nonaccumulation_contract": {
            "acceptable_fixed_shift": (
                "E_metric,s(t)<=C_T E_aux,s+r(0) with one fixed r for the "
                "whole evolution and iteration"
            ),
            "unacceptable_iterative_shift": (
                "E_s[U_(n+1)]<=C E_(s+1)[U_n], which demands s+n "
                "derivatives after n iterations"
            ),
            "one_time_loss_established": False,
            "loss_nonaccumulation_established": False,
            "picard_closure_established": False,
            "nash_moser_required": "UNRESOLVED",
        },
        "regularity_threshold_ledger": {
            "spatial_dimension": 3,
            "analytic_floor": "s>5/2 for C^1 coefficient control",
            "frozen_integer_candidate": "s>=3",
            "variable_and_quasilinear_working_candidate": "s>=4",
            "requirements": [
                "uniform Lorentzian coefficient bounds",
                "C^1 control of g and coefficient fields",
                "H^s algebra and product estimates",
                "Kato-Ponce or Moser commutators",
                "metric-curvature reconstruction",
                "69-component constraint propagation",
                "one spare derivative for the candidate fixed loss",
            ],
            "minimum_index_established": False,
            "candidate_is_not_theorem": True,
        },
        "level_1_execution_acceptance_tests": [
            "Exact 128-component first-order-in-time companion ordering is frozen.",
            "Every one of the 50 chains at each root is mapped into companion variables.",
            "The Fourier exponential is computed without dropping lower triangular resonant terms.",
            "Growth exponents are proved uniformly for every normalized spatial direction.",
            "Physical TT and non-TT chain losses are reported separately.",
            "Constraint-tangent and transverse subspaces are projected explicitly.",
            "The minimum r is reported as 0, 1, 2, or blocked.",
            "No variable-coefficient or quasilinear conclusion is inferred.",
        ],
        "permitted_future_outcomes": [
            "ADAPTED_ENERGY_HIERARCHY_READY",
            "JORDAN_CHAIN_LOSS_GRADING_UNRESOLVED",
            "CANDIDATE_LOSS_REVISED_TO_TWO_DERIVATIVES",
            "LOWER_ORDER_WEIGHTED_PRINCIPAL_CONTAMINATION",
            "FIXED_LINEAR_LOSS_BUT_QUASILINEAR_CLOSURE_UNRESOLVED",
            "NASH_MOSER_ROUTE_REQUIRED",
            "ADAPTED_ENERGY_ROUTE_BLOCKED",
        ],
        "preparation_outcomes": [
            "ADAPTED_ENERGY_HIERARCHY_READY",
            "JORDAN_CHAIN_LOSS_GRADING_UNRESOLVED",
            "KNOWN_WEIGHTED_PRINCIPAL_CONTAMINATION_INCLUDED_NOT_YET_ESTIMATED",
        ],
        "literature_boundary": {
            "arxiv_2607_11879": (
                "Supports the physical q^2 spin-2 obstruction, the absence "
                "of a same-order metric estimate for arbitrary lower terms, "
                "and the warning that finite-loss estimates are sensitive "
                "to lower-order structure. It does not prove this packet's "
                "candidate adapted estimate."
            ),
            "arxiv_1811_07869": (
                "Supports smooth-solution and maximal-development results "
                "for a harmonic nonlinear-wave formulation. It does not "
                "supply the frozen companion growth or Sobolev stability "
                "estimate demanded here."
            ),
        },
        "claim_boundary": {
            "energy_norms_frozen": True,
            "all_fifty_chains_each_root_ledgered": True,
            "raw_jordan_growth_ceilings_recorded": True,
            "equivalence_map_shift_one_derivative": True,
            "propagator_loss_one_derivative_established": False,
            "propagator_loss_two_derivatives_refuted": False,
            "frozen_coefficient_energy_estimate_established": False,
            "variable_coefficient_energy_estimate_established": False,
            "quasilinear_tame_estimate_established": False,
            "loss_nonaccumulation_established": False,
            "picard_iteration_closed": False,
            "nash_moser_required": False,
            "local_existence_established": False,
            "uniqueness_established": False,
            "continuous_dependence_established": False,
            "source_extension_executed": False,
        },
        "prohibitions_respected": {
            "energy_estimate_claimed_from_principal_symbol": False,
            "jordan_length_used_as_companion_growth_proof": False,
            "one_derivative_equivalence_shift_called_propagator_loss": False,
            "constraints_used_to_repair_physical_defect": False,
            "order_reduction_claimed_as_original_theory": False,
            "regularizer_or_fiducial_mode_added": False,
            "ghost_analysis_executed": False,
            "phenomenology_executed": False,
            "source_extension_executed": False,
            "yukawa_work_executed": False,
        },
        "selected_next_target": REVIEW_TARGET,
        "verdict": (
            "ENERGY_HIERARCHY_AND_COMPLETE_JORDAN_LEDGER_PREPARED_"
            "ONE_DERIVATIVE_EQUIVALENCE_SHIFT_DISTINGUISHED_FROM_"
            "UNRESOLVED_ONE_OR_TWO_DERIVATIVE_PROPAGATOR_LOSS_NO_"
            "ENERGY_OR_WELL_POSEDNESS_CLAIM"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_packet,
        description=(
            "quadratic-gravity adapted derivative-loss energy-hierarchy "
            "preparation"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
