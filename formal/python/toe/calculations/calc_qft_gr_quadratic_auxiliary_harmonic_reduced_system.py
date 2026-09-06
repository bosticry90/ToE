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


PACKET_REVIEW_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_AUXILIARY_HARMONIC_ADAPTED_NORM_"
    "WELL_POSEDNESS_PACKET_RESULT_REVIEW_20260728_v0.json"
)
SOURCE_PACKET_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_HYPERBOLICITY_ADMISSIBLE_SOURCE_AND_"
    "FROZEN_THEORY_PACKET_20260728_v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-QFT-GR-QUADRATIC-AUXILIARY-HARMONIC-REDUCED-SYSTEM-v0.json"
)
CURRENT_TARGET = (
    "derive_qft_gr_quadratic_auxiliary_harmonic_reduced_system_v0"
)
RESULT_REVIEW_TARGET = (
    "review_qft_gr_quadratic_auxiliary_harmonic_reduced_system_v0_result"
)


def derive_projection_coefficients() -> dict:
    alpha, beta = sp.symbols("alpha beta")
    gamma = 3 * alpha + beta

    trace_box = sp.expand(6 * alpha + 2 * beta)
    tf_hessian = sp.expand(-(2 * alpha + beta))
    tf_scalar_tensor = sp.expand(2 * alpha + beta / 2)
    kinetic_determinant = sp.factor(2 * gamma * beta)
    return {
        "gamma": sp.sstr(gamma),
        "trace_box_coefficient": sp.sstr(trace_box),
        "trace_box_factorization": sp.sstr(sp.factor(trace_box)),
        "trace_free_tensor_box_coefficient": sp.sstr(beta),
        "trace_free_hessian_coefficient": sp.sstr(tf_hessian),
        "trace_free_R_times_S_coefficient": sp.sstr(tf_scalar_tensor),
        "trace_free_Riemann_times_S_coefficient": sp.sstr(2 * beta),
        "trace_free_metric_times_S_squared_coefficient": sp.sstr(-beta / 2),
        "kinetic_map_determinant": sp.sstr(kinetic_determinant),
        "kinetic_map_invertible_iff": [
            "beta != 0",
            "3 alpha + beta != 0",
        ],
    }


def build_calculation() -> dict:
    packet_review = read_json(PACKET_REVIEW_PATH)
    source_packet = read_json(SOURCE_PACKET_PATH)
    if packet_review["accepted"] is not True:
        raise QuadraticHyperbolicityError(
            "auxiliary-harmonic preparation packet was not accepted"
        )
    if packet_review["selected_next_target"] != CURRENT_TARGET:
        raise QuadraticHyperbolicityError(
            "reduced-system derivation authority mismatch"
        )
    coefficients = derive_projection_coefficients()
    if coefficients["kinetic_map_determinant"] != (
        "2*beta*(3*alpha + beta)"
    ):
        raise QuadraticHyperbolicityError(
            "unexpected trace/trace-free kinetic determinant"
        )

    original_equation = (
        "E_mn := c_R(R_mn-(1/2)g_mn R) -(1/2)c_Lambda g_mn "
        "+ alpha[2 R R_mn -(1/2)g_mn R^2 "
        "+2(g_mn Box_g-nabla_m nabla_n)R] "
        "+ beta[2 R_mrns R^rs -(1/2)g_mn R_rs R^rs "
        "+Box_g R_mn +(1/2)g_mn Box_g R "
        "-nabla_m nabla_n R] = 0"
    )
    scalar_equation = (
        "E_R := 2(3 alpha+beta) Box_g R - c_R R "
        "- 2 c_Lambda = 0"
    )
    spin2_equation = (
        "E_S_mn := beta Box_g S_mn "
        "-(2 alpha+beta)(nabla_m r_n-(1/4)g_mn Box_g R) "
        "+[c_R+(2 alpha+beta/2)R]S_mn "
        "+2 beta R_mrns[g,c] S^rs "
        "-(beta/2)g_mn S_rs S^rs = 0"
    )

    return {
        "schema_id": (
            "CALC_QFT_GR_QUADRATIC_AUXILIARY_HARMONIC_"
            "REDUCED_SYSTEM_v0"
        ),
        "calculation_id": (
            "CALC-QFT-GR-QUADRATIC-AUXILIARY-HARMONIC-"
            "REDUCED-SYSTEM-v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "execution_target": CURRENT_TARGET,
        "consumed_authority": {
            "path": PACKET_REVIEW_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(PACKET_REVIEW_PATH),
            "accepted": packet_review["accepted"],
        },
        "consumed_frozen_conventions": {
            "path": SOURCE_PACKET_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(SOURCE_PACKET_PATH),
            "riemann": source_packet["frozen_conventions"]["riemann"],
            "ricci": source_packet["frozen_conventions"]["ricci"],
        },
        "frozen_scope": {
            "dimension": 4,
            "metric_signature": "(-,+,+,+)",
            "action_density": (
                "sqrt(-g)[c_R R+c_Lambda+alpha R^2+beta R_mn R^mn]"
            ),
            "source": "VACUUM",
            "gauge": "PRESCRIBED_GENERALIZED_HARMONIC",
            "gauge_source": (
                "H^mu=H^mu(x,g), prescribed C^2, with no dependence on "
                "partial g or higher derivatives"
            ),
            "generic_principal_sector": [
                "beta != 0",
                "3 alpha + beta != 0",
            ],
            "einstein_connected_sector_adds": "c_R != 0",
        },
        "original_metric_equation": {
            "equation": original_equation,
            "vacuum_bianchi_identity": "nabla^m E_mn identically equals 0",
            "differential_order_in_metric": 4,
        },
        "projection_derivation": {
            "definition": "S_mn := R_mn-(1/4)g_mn R",
            "trace_constraint": "g^mn S_mn = 0",
            "ricci_decomposition": "R_mn = S_mn+(1/4)g_mn R",
            "ricci_square_decomposition": (
                "R_mn R^mn = S_mn S^mn+(1/4)R^2"
            ),
            "trace_equation": scalar_equation,
            "trace_free_equation": spin2_equation,
            "coefficient_ledger": coefficients,
            "reconstruction_identity": (
                "E_mn = E_S_mn+(1/4)g_mn(g^rs E_rs), "
                "with g^rs E_rs=E_R"
            ),
        },
        "auxiliary_variables": [
            {
                "symbol": "g_mn",
                "components": 10,
                "role": "Lorentzian metric",
                "new_physical_mode": False,
            },
            {
                "symbol": "R",
                "components": 1,
                "definition": "scalar curvature of g on the constraint set",
                "new_physical_mode": False,
            },
            {
                "symbol": "r_a",
                "components": 4,
                "definition": "partial_a R",
                "role": "derivative closure variable",
                "new_physical_mode": False,
            },
            {
                "symbol": "c_mna",
                "components": 40,
                "definition": "partial_a g_mn, symmetric in mn",
                "role": "derivative closure variable",
                "new_physical_mode": False,
            },
            {
                "symbol": "S_mn",
                "components": 9,
                "definition": (
                    "R_mn[g]-(1/4)g_mn scalar_curvature[g] "
                    "on the constraint set"
                ),
                "role": "trace-free Ricci auxiliary",
                "new_physical_mode": False,
            },
        ],
        "exact_operator_definitions": {
            "inverse_metric_derivative": (
                "partial_a g^mn = -g^mr g^ns c_rsa"
            ),
            "connection": (
                "Gamma^r_mn := (1/2)g^rs"
                "(c_snm+c_smn-c_mns)"
            ),
            "contracted_connection": "Gamma^r := g^mn Gamma^r_mn",
            "gauge_constraint": "C_H^r := Gamma^r-H^r(x,g)",
            "riemann": (
                "R^r_smn[g,c] := partial_m Gamma^r_ns "
                "-partial_n Gamma^r_ms "
                "+Gamma^r_ml Gamma^l_ns "
                "-Gamma^r_nl Gamma^l_ms"
            ),
            "ricci": "R_sn[g,c] := R^r_srn[g,c]",
            "lowered_riemann": "R_mrns[g,c] := g_ml R^l_rns[g,c]",
            "component_wave": (
                "W_g u := g^ab partial_a partial_b u, component by component"
            ),
            "scalar_box": (
                "Box_g R := W_g R-Gamma^a r_a"
            ),
            "scalar_hessian": (
                "nabla_m r_n := partial_m r_n-Gamma^a_mn r_a"
            ),
            "trace_free_hessian": (
                "(nabla_m r_n)^TF := nabla_m r_n "
                "-(1/4)g_mn Box_g R"
            ),
            "tensor_first_derivative": (
                "D_a S_mn := partial_a S_mn "
                "-Gamma^r_am S_rn-Gamma^r_an S_mr"
            ),
            "tensor_second_derivative": (
                "D_a D_b S_mn := partial_a(D_b S_mn) "
                "-Gamma^r_ab D_r S_mn "
                "-Gamma^r_am D_b S_rn "
                "-Gamma^r_an D_b S_mr"
            ),
            "tensor_box": "Box_g S_mn := g^ab D_a D_b S_mn",
            "tensor_box_remainder": (
                "L^S_mn(g,c,partial c,S,partial S) := "
                "Box_g S_mn-W_g S_mn"
            ),
            "harmonic_ricci_remainder": (
                "Q_mn(g,c) := R_mn[g] +(1/2)W_g g_mn "
                "-(1/2)(g_mr partial_n Gamma^r "
                "+g_nr partial_m Gamma^r); all partial c terms cancel"
            ),
            "generalized_harmonic_remainder": (
                "Q^H_mn := Q_mn(g,c) "
                "+(1/2)(g_mr partial_n H^r+g_nr partial_m H^r)"
            ),
            "reduced_ricci": (
                "R^H_mn := -(1/2)W_g g_mn+Q^H_mn"
            ),
        },
        "closed_second_order_system": {
            "unknown_vector": ["g_mn", "R", "r_a", "c_mna", "S_mn"],
            "metric_equation": {
                "id": "E_g^H",
                "covariant_form": (
                    "R^H_mn = S_mn+(1/4)g_mn R"
                ),
                "coordinate_form": (
                    "W_g g_mn = F^g_mn := "
                    "2Q^H_mn-2S_mn-(1/2)g_mn R"
                ),
            },
            "scalar_equation": {
                "id": "E_R",
                "covariant_form": scalar_equation,
                "coordinate_form": (
                    "W_g R = F^R := Gamma^a r_a "
                    "+(c_R R+2c_Lambda)/[2(3alpha+beta)]"
                ),
            },
            "scalar_derivative_equation": {
                "id": "E_r",
                "equation": (
                    "W_g r_a = F^r_a := partial_a F^R "
                    "-(partial_a g^bc)partial_b r_c"
                ),
                "origin": "partial_a(E_R coordinate form)",
            },
            "metric_derivative_equation": {
                "id": "E_c",
                "equation": (
                    "W_g c_mna = F^c_mna := partial_a F^g_mn "
                    "-(partial_a g^bc)partial_b c_mnc"
                ),
                "origin": "partial_a(E_g^H coordinate form)",
            },
            "trace_free_ricci_equation": {
                "id": "E_S",
                "covariant_form": spin2_equation,
                "coordinate_form": (
                    "W_g S_mn = beta^(-1){"
                    "(2alpha+beta)(nabla_m r_n)^TF "
                    "-[c_R+(2alpha+beta/2)R]S_mn "
                    "-2beta R_mrns[g,c]S^rs "
                    "+(beta/2)g_mn S_rs S^rs} - L^S_mn"
                ),
            },
            "principal_organization": (
                "Each displayed evolution equation has W_g acting on its "
                "own unknown; every right-hand side is an exact function "
                "of U and partial U after the definitions above are expanded."
            ),
            "not_an_order_reduction_of_the_physics": (
                "The enlarged system is equivalent to the original "
                "fourth-order metric equation only on the complete "
                "definition-and-gauge constraint surface."
            ),
        },
        "constraint_system": [
            {
                "id": "C_H^a",
                "equation": "Gamma^a-H^a(x,g)=0",
                "class": "generalized-harmonic gauge",
            },
            {
                "id": "C_r_a",
                "equation": "r_a-partial_a R=0",
                "class": "scalar derivative definition",
            },
            {
                "id": "C_c_mna",
                "equation": "c_mna-partial_a g_mn=0",
                "class": "metric derivative definition",
            },
            {
                "id": "C_R",
                "equation": "R-g^mn R_mn[g,c]=0",
                "class": "scalar-curvature definition",
            },
            {
                "id": "C_S_mn",
                "equation": (
                    "S_mn-[R_mn[g,c]-(1/4)g_mn g^rs R_rs[g,c]]=0"
                ),
                "class": "trace-free Ricci definition",
            },
            {
                "id": "C_trace",
                "equation": "g^mn S_mn=0",
                "class": "algebraic trace",
            },
            {
                "id": "C_div_n",
                "equation": "nabla^m S_mn-(1/4)r_n=0",
                "class": "contracted-Bianchi compatibility",
            },
            {
                "id": "C_curl_r_ab",
                "equation": "partial_a r_b-partial_b r_a=0",
                "class": "scalar derivative integrability",
            },
            {
                "id": "C_curl_c_mnab",
                "equation": (
                    "partial_a c_mnb-partial_b c_mna=0"
                ),
                "class": "metric derivative integrability",
            },
            {
                "id": "C_Hamiltonian",
                "equation": "n^m n^n E_mn=0",
                "class": "normal-normal original metric projection",
            },
            {
                "id": "C_momentum_a",
                "equation": "h^n_a n^m E_mn=0",
                "class": "normal-tangential original metric projection",
            },
        ],
        "initial_data_contract": {
            "raw_second_order_data": (
                "U|Sigma and n^a partial_a U|Sigma for "
                "U=(g,R,r,c,S)"
            ),
            "unconstrained_seed_fields_before_constraint_solving": [
                "g_mn and normal derivative of g_mn",
                "R and normal derivative of R",
                "trace-free S_mn and normal derivative of S_mn",
            ],
            "definition_derived_fields": [
                "r_a and its normal derivative from C_r and E_R",
                "c_mna and its normal derivative from C_c and E_g^H",
            ],
            "not_freely_specifiable_on_metric_equivalence_surface": [
                "R data, which must satisfy C_R",
                "S_mn data, which must satisfy C_S, C_trace, and C_div",
                "g_mn data, which must satisfy gauge, Hamiltonian, and momentum constraints",
            ],
            "freely_specifiable_component_parametrization": (
                "NOT_CLASSIFIED_HERE; solving and parametrizing the coupled "
                "constraint manifold belongs to the propagation/initial-data "
                "successor and cannot be inferred from raw component counts"
            ),
            "compatibility_required": [
                "C_H and its normal derivative",
                "C_R and C_S",
                "C_trace and C_div",
                "C_curl_r and C_curl_c",
                "C_Hamiltonian and C_momentum",
            ],
            "arbitrary_auxiliary_data_are_original_metric_data": False,
        },
        "derivative_ledger": [
            {
                "equation": "E_g^H",
                "unknown": "g_mn",
                "highest_time_derivative": 2,
                "highest_spatial_derivative": 2,
                "rhs_highest_derivative_of_U": 0,
                "source_regularity_required": "none (vacuum)",
                "constraint_derivative_order": (
                    "C_H and C_c are first order; C_R and C_S are second "
                    "order in the metric"
                ),
                "metric_only_interpretation": "g order 2",
            },
            {
                "equation": "E_R",
                "unknown": "R",
                "highest_time_derivative": 2,
                "highest_spatial_derivative": 2,
                "rhs_highest_derivative_of_U": 0,
                "source_regularity_required": "none (vacuum)",
                "constraint_derivative_order": (
                    "C_r is first order in R; C_R is second order in g"
                ),
                "metric_only_interpretation": "g order 4",
            },
            {
                "equation": "E_r",
                "unknown": "r_a",
                "highest_time_derivative": 2,
                "highest_spatial_derivative": 2,
                "rhs_highest_derivative_of_U": 1,
                "source_regularity_required": "none (vacuum)",
                "constraint_derivative_order": (
                    "C_r and C_curl_r are first order in reduced variables"
                ),
                "metric_only_interpretation": "g order 5",
            },
            {
                "equation": "E_c",
                "unknown": "c_mna",
                "highest_time_derivative": 2,
                "highest_spatial_derivative": 2,
                "rhs_highest_derivative_of_U": 1,
                "source_regularity_required": "none (vacuum)",
                "constraint_derivative_order": (
                    "C_c and C_curl_c are first order in reduced variables"
                ),
                "metric_only_interpretation": "g order 3",
            },
            {
                "equation": "E_S",
                "unknown": "S_mn",
                "highest_time_derivative": 2,
                "highest_spatial_derivative": 2,
                "rhs_highest_derivative_of_U": 1,
                "source_regularity_required": "none (vacuum)",
                "constraint_derivative_order": (
                    "C_trace is algebraic, C_div is first order, and C_S "
                    "is second order in g"
                ),
                "metric_only_interpretation": "g order 4",
            },
        ],
        "equivalence_boundary": {
            "metric_to_auxiliary": (
                "A C^4 solution g of E_mn=0 in the prescribed generalized-"
                "harmonic gauge induces R, r, c, and S by their definitions "
                "and satisfies E_g^H, E_R, E_r, E_c, and E_S."
            ),
            "auxiliary_to_metric": (
                "A sufficiently regular auxiliary solution satisfying every "
                "definition, trace, divergence, integrability, gauge, "
                "Hamiltonian, and momentum constraint reconstructs "
                "R_mn=S_mn+(1/4)g_mn R; E_R=0 and E_S=0 then reconstruct "
                "E_mn=0 by trace plus trace-free decomposition."
            ),
            "arbitrary_auxiliary_solution_to_metric_solution": False,
            "constraint_propagation_established_here": False,
            "next_required_proof": (
                "derive the closed homogeneous gauge and auxiliary-"
                "constraint propagation system"
            ),
        },
        "coefficient_controls": {
            "beta_eq_0": (
                "E_S cannot be solved as a wave equation; generic reduction "
                "rank changes."
            ),
            "3alpha_plus_beta_eq_0": (
                "E_R cannot be solved as a scalar wave equation; generic "
                "reduction rank changes."
            ),
            "alpha_eq_beta_eq_0": (
                "Einstein second-order control; not in the generic reduction."
            ),
            "c_R_eq_0": (
                "Reduction remains algebraically invertible when beta and "
                "3alpha+beta are nonzero, but the sector is not "
                "Einstein-connected."
            ),
            "c_Lambda": "lower order in every principal block",
        },
        "claim_boundary": {
            "exact_reduced_equations_derived": True,
            "algebraic_equivalence_on_full_constraint_surface_derived": True,
            "constraint_propagation_established": False,
            "reduced_system_principal_symbol_classified": False,
            "one_derivative_loss_sufficient": False,
            "linear_energy_estimate_established": False,
            "picard_iteration_closed": False,
            "local_well_posedness_established": False,
            "ordinary_metric_strong_hyperbolicity_restored": False,
            "source_extension_executed": False,
        },
        "prohibitions_respected": {
            "perturbative_order_reduction": False,
            "regularizer_added": False,
            "fiducial_mode_added": False,
            "new_physical_mode_added": False,
            "numerical_stability_substituted": False,
            "preserved_descendant_adopted": False,
            "yukawa_work_executed": False,
        },
        "selected_next_target": RESULT_REVIEW_TARGET,
        "verdict": (
            "EXACT_VACUUM_AUXILIARY_HARMONIC_REDUCED_SYSTEM_DERIVED_"
            "CONSTRAINT_PROPAGATION_AND_WELL_POSEDNESS_NOT_ESTABLISHED"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_calculation,
        description=(
            "quadratic-gravity auxiliary harmonic reduced-system calculation"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
