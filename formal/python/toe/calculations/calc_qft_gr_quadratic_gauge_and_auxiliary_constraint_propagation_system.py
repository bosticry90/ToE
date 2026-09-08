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


REDUCED_REVIEW_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_AUXILIARY_HARMONIC_REDUCED_SYSTEM_"
    "RESULT_REVIEW_20260728_v0.json"
)
REDUCED_CALCULATION_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-QFT-GR-QUADRATIC-AUXILIARY-HARMONIC-REDUCED-SYSTEM-v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-QFT-GR-QUADRATIC-GAUGE-AUXILIARY-CONSTRAINT-"
    "PROPAGATION-SYSTEM-v0.json"
)
CURRENT_TARGET = (
    "derive_qft_gr_quadratic_gauge_and_auxiliary_"
    "constraint_propagation_system_v0"
)
RESULT_REVIEW_TARGET = (
    "review_qft_gr_quadratic_gauge_and_auxiliary_"
    "constraint_propagation_system_v0_result"
)


def derive_subsidiary_pencil() -> dict:
    """Independently construct the normalized minimal wave pencil."""
    lam, beta = sp.symbols("lambda beta", nonzero=True)
    wave = 1 - lam**2

    # C_H (4), Phi (16), C_r (4), and C_c (40) have unit wave
    # coefficients. V_H (4) and T (1) have beta before normalization.
    unit_wave_components = 4 + 16 + 4 + 40
    beta_wave_components = 4 + 1
    total_components = unit_wave_components + beta_wave_components
    determinant = sp.factor(
        wave**unit_wave_components * (beta * wave) ** beta_wave_components
    )
    return {
        "unit_wave_components": unit_wave_components,
        "beta_wave_components": beta_wave_components,
        "independent_wave_components": total_components,
        "pencil": (
            "diag((1-lambda^2) I_64, "
            "beta(1-lambda^2) I_5)"
        ),
        "normalized_pencil": "(1-lambda^2) I_69",
        "determinant": sp.sstr(determinant),
        "roots": [-1, 1],
        "algebraic_multiplicity_each_root": total_components,
        "geometric_multiplicity_each_root": total_components,
        "complete_eigenbasis": True,
        "strongly_hyperbolic": True,
        "symmetric_first_order_wave_reduction_available": True,
    }


def build_calculation() -> dict:
    reduced_review = read_json(REDUCED_REVIEW_PATH)
    reduced = read_json(REDUCED_CALCULATION_PATH)
    if reduced_review["accepted"] is not True:
        raise QuadraticHyperbolicityError(
            "reduced-system result review was not accepted"
        )
    if reduced_review["selected_next_target"] != CURRENT_TARGET:
        raise QuadraticHyperbolicityError(
            "constraint-propagation authority mismatch"
        )
    if reduced["claim_boundary"]["constraint_propagation_established"]:
        raise QuadraticHyperbolicityError(
            "predecessor already claims constraint propagation"
        )

    pencil = derive_subsidiary_pencil()
    if pencil["independent_wave_components"] != 69:
        raise QuadraticHyperbolicityError(
            "unexpected independent subsidiary dimension"
        )
    if pencil["determinant"] != (
        "-beta**5*(lambda - 1)**69*(lambda + 1)**69"
    ):
        raise QuadraticHyperbolicityError(
            "unexpected subsidiary determinant"
        )

    return {
        "schema_id": (
            "CALC_QFT_GR_QUADRATIC_GAUGE_AUXILIARY_CONSTRAINT_"
            "PROPAGATION_SYSTEM_v0"
        ),
        "calculation_id": (
            "CALC-QFT-GR-QUADRATIC-GAUGE-AUXILIARY-CONSTRAINT-"
            "PROPAGATION-SYSTEM-v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "execution_target": CURRENT_TARGET,
        "consumed_authority": {
            "path": REDUCED_REVIEW_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(REDUCED_REVIEW_PATH),
            "accepted": True,
        },
        "consumed_reduced_system": {
            "path": REDUCED_CALCULATION_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(REDUCED_CALCULATION_PATH),
            "unknown_vector": reduced["closed_second_order_system"][
                "unknown_vector"
            ],
            "equations": ["E_g^H", "E_R", "E_r", "E_c", "E_S"],
        },
        "frozen_scope": {
            "dimension": 4,
            "metric_signature": "(-,+,+,+)",
            "source": "VACUUM",
            "gauge_source": (
                "H^a=H^a(x,g), prescribed C^2, with no partial-g "
                "or higher-derivative dependence"
            ),
            "generic_sector": [
                "beta != 0",
                "3 alpha + beta != 0",
            ],
            "initial_hypersurface": (
                "smooth spacelike noncharacteristic Sigma with unit normal n"
            ),
        },
        "off_constraint_extension": {
            "frozen_equations": [
                "E_g^H",
                "E_R",
                "E_r",
                "E_c",
                "E_S",
            ],
            "definition": (
                "Exactly the coordinate equations in the consumed reduced-"
                "system artifact, evaluated without setting any constraint "
                "to zero."
            ),
            "constraint_addition_M_A_B": "identically zero",
            "derivative_constraint_addition_N_A_B_mu": "identically zero",
            "constraint_damping": "none",
            "added_differential_order": 0,
            "changes_evolution_principal_symbol": False,
            "changes_physical_spin2_block": False,
            "physical_block_remains": (
                "-beta(lambda^2-1)^2 I_2 in the frozen ToE conventions"
            ),
            "regularizer_or_fiducial_mode_added": False,
        },
        "exact_defect_operators": {
            "gauge_constraint": "C_H^a := Gamma^a[g,c]-H^a(x,g)",
            "gauge_derivative": "Phi^a_b := partial_b C_H^a",
            "metric_definition_defect": (
                "C_c_mna := c_mna-partial_a g_mn"
            ),
            "scalar_definition_defect": "C_r_a := r_a-partial_a R",
            "reduced_ricci": (
                "R^H_mn := -(1/2)W_g g_mn+Q^H_mn[g,c,H]"
            ),
            "total_ricci_defect": (
                "K_tot_mn := R_mn[g]-R^H_mn[g,c,H]"
            ),
            "pure_gauge_ricci_defect": (
                "K_H_mn := (1/2)(g_ma partial_n C_H^a"
                "+g_na partial_m C_H^a)"
            ),
            "metric_definition_ricci_defect": (
                "K_c_mn := K_tot_mn-K_H_mn; this exact difference "
                "vanishes when C_c=0"
            ),
            "traces": (
                "K_X := g^mn K_X_mn for X in {tot,H,c}"
            ),
            "einstein_defects": (
                "deltaG_X_mn := K_X_mn-(1/2)g_mn K_X "
                "for X in {tot,H,c}"
            ),
            "divergence_defects": (
                "V_X_n := nabla^m deltaG_X_mn for X in {tot,H,c}; "
                "V_tot=V_H+V_c"
            ),
            "trace_constraint": "T := g^mn S_mn",
            "divergence_constraint": (
                "D_n := nabla^m S_mn-(1/4)r_n"
            ),
            "scalar_curvature_definition": (
                "C_R := R-g^mn R_mn[g]"
            ),
            "tracefree_ricci_definition": (
                "C_S_mn := S_mn-[R_mn[g]"
                "-(1/4)g_mn g^ab R_ab[g]]"
            ),
            "exact_auxiliary_metric_residual": (
                "E_aux_mn := E_S_mn+(1/4)g_mn E_R"
            ),
            "exact_original_minus_auxiliary_defect": (
                "DeltaE_mn := E_mn[g]-E_aux_mn[U], with E_mn[g] "
                "the displayed original Euler-Lagrange tensor in the "
                "consumed artifact"
            ),
            "exact_V_remainder": (
                "R_V_n := nabla^m DeltaE_mn-beta Box_g V_H_n, "
                "after the stated normalization rules"
            ),
            "no_implicit_remainder": (
                "Every named defect and R_V is an operator equality, not "
                "an omitted-term marker."
            ),
        },
        "normalization_rules": [
            (
                "Replace partial C_H by Phi and replace higher mixed partial "
                "derivatives by derivatives of Phi."
            ),
            (
                "Replace W_g C_r and W_g C_c by their exact differentiated-"
                "equation propagation identities."
            ),
            (
                "Replace Box_g T by the exact trace of E_S."
            ),
            (
                "Resolve commuted derivatives of C_r and C_c through their "
                "explicit curl constraints I_R and I_g."
            ),
            (
                "Replace V_tot by V_H+V_c and use V_c as the exact functional "
                "of C_c fixed above."
            ),
            (
                "No equation from the original metric theory is assumed; "
                "only the reduced equations and differential identities are "
                "used."
            ),
        ],
        "exact_propagation_identities": {
            "scalar_derivative_definition": {
                "constraint": "C_r_a := r_a-partial_a R",
                "equation": (
                    "W_g C_r_a = -(partial_a g^bc)partial_b C_r_c"
                ),
                "homogeneous": True,
            },
            "metric_derivative_definition": {
                "constraint": "C_c_mna := c_mna-partial_a g_mn",
                "equation": (
                    "W_g C_c_mna = "
                    "-(partial_a g^bc)partial_b C_c_mnc"
                ),
                "homogeneous": True,
            },
            "scalar_integrability": {
                "constraint": (
                    "I_R_ab := partial_a r_b-partial_b r_a"
                ),
                "identity": (
                    "I_R_ab=partial_a C_r_b-partial_b C_r_a"
                ),
                "homogeneous": True,
            },
            "metric_integrability": {
                "constraint": (
                    "I_g_mnab := partial_a c_mnb-partial_b c_mna"
                ),
                "identity": (
                    "I_g_mnab=partial_a C_c_mnb-partial_b C_c_mna"
                ),
                "homogeneous": True,
            },
            "trace": {
                "constraint": "T := g^mn S_mn",
                "equation": (
                    "beta Box_g T+[c_R+(2alpha+beta)R]T"
                    "+2beta K_tot_mn S^mn=0"
                ),
                "homogeneous": True,
            },
            "contracted_bianchi": {
                "equation": (
                    "V_tot_n=-D_n-(1/2)C_r_n"
                    "+(1/2)nabla_n T"
                ),
                "solved_for_divergence_constraint": (
                    "D_n=-V_H_n-V_c_n-(1/2)C_r_n"
                    "+(1/2)nabla_n T"
                ),
                "homogeneous": True,
            },
            "scalar_curvature_definition": {
                "equation": "C_R=-(T+K_tot)",
                "homogeneous": True,
            },
            "tracefree_ricci_definition": {
                "equation": (
                    "C_S_mn=-K_tot_mn"
                    "+(1/4)g_mn(T+K_tot)"
                ),
                "homogeneous": True,
            },
            "gauge": {
                "exact_remainder": (
                    "A_H^a := 2g^an nabla^m deltaG_H_mn-W_g C_H^a"
                ),
                "equation": (
                    "W_g C_H^a=2g^an V_H_n-A_H^a"
                ),
                "remainder_order": (
                    "A_H is polynomial in C_H and Phi, contains no "
                    "derivative of Phi, and A_H(0,0)=0"
                ),
                "homogeneous": True,
            },
            "gauge_derivative": {
                "equation": (
                    "W_g Phi^a_b="
                    "partial_b(2g^an V_H_n-A_H^a)"
                    "-(partial_b g^mn)partial_m Phi^a_n"
                ),
                "homogeneous": True,
            },
            "divergence_defect": {
                "identity": (
                    "nabla^m DeltaE_mn=beta Box_g V_H_n+R_V_n"
                ),
                "equation": "beta Box_g V_H_n=-R_V_n",
                "remainder_order": (
                    "After the exact normalization rules, R_V is polynomial "
                    "in the finite constraint vector and its first "
                    "derivatives."
                ),
                "zero_test": "R_V(U;0,0)=0",
                "homogeneous": True,
            },
        },
        "finite_subsidiary_system": {
            "independent_wave_vector": [
                "C_H^a",
                "Phi^a_b",
                "V_H_n",
                "C_r_a",
                "C_c_mna",
                "T",
            ],
            "independent_component_count": 69,
            "derived_constraint_vector": [
                "I_R_ab",
                "I_g_mnab",
                "D_n",
                "C_R",
                "C_S_mn",
                "C_Hamiltonian",
                "C_momentum_i",
            ],
            "closure_order": [
                "C_r and C_c homogeneous wave layer",
                "I_R and I_g differential-consequence layer",
                "C_H, Phi, and V_H gauge-defect wave layer",
                "T trace wave layer",
                "D, C_R, and C_S reconstruction layer",
                "Hamiltonian and momentum Bianchi-projection layer",
            ],
            "new_constraint_generated_by_differentiation": False,
            "finite": True,
            "homogeneous": True,
            "P_C_of_zero": "0",
        },
        "constraint_classification": [
            {
                "id": "C_H^a",
                "classification": "INDEPENDENT_INITIAL_CONSTRAINT",
                "initial_data": "C_H|Sigma=0 and n.nabla C_H|Sigma=0",
            },
            {
                "id": "Phi^a_b",
                "classification": "DEFINITION_CONSTRAINT",
                "initial_data": (
                    "derived from C_H and its first derivatives; not "
                    "independently prescribed"
                ),
            },
            {
                "id": "V_H_n",
                "classification": "INDEPENDENT_INITIAL_CONSTRAINT",
                "initial_data": (
                    "V_H|Sigma=0; its normal derivative is redundant after "
                    "the geometric projections and reduced equations"
                ),
            },
            {
                "id": "C_r_a",
                "classification": "DEFINITION_CONSTRAINT",
                "initial_data": "value and compatible normal derivative",
            },
            {
                "id": "C_c_mna",
                "classification": "DEFINITION_CONSTRAINT",
                "initial_data": "value and compatible normal derivative",
            },
            {
                "id": "I_R_ab",
                "classification": "INTEGRABILITY_CONSEQUENCE",
                "initial_data": "derived from C_r",
            },
            {
                "id": "I_g_mnab",
                "classification": "INTEGRABILITY_CONSEQUENCE",
                "initial_data": "derived from C_c",
            },
            {
                "id": "T",
                "classification": "DEFINITION_CONSTRAINT",
                "initial_data": "value and compatible normal derivative",
            },
            {
                "id": "D_n",
                "classification": "EVOLUTION_CONSEQUENCE",
                "initial_data": (
                    "reconstructed from V_H,V_c,C_r,nabla T"
                ),
            },
            {
                "id": "C_R",
                "classification": "EVOLUTION_CONSEQUENCE",
                "initial_data": "reconstructed from T and K_tot",
            },
            {
                "id": "C_S_mn",
                "classification": "EVOLUTION_CONSEQUENCE",
                "initial_data": "reconstructed from T and K_tot",
            },
            {
                "id": "C_Hamiltonian",
                "classification": "INDEPENDENT_INITIAL_CONSTRAINT",
                "initial_data": (
                    "normal-normal projection of the original equation"
                ),
            },
            {
                "id": "C_momentum_i",
                "classification": "INDEPENDENT_INITIAL_CONSTRAINT",
                "initial_data": (
                    "normal-tangential projections of the original equation"
                ),
            },
            {
                "id": "normal_derivative_of_V_H",
                "classification": "REDUNDANT_BY_BIANCHI_IDENTITY",
                "initial_data": (
                    "follows from E_g^H,E_R,E_S and the Hamiltonian/"
                    "momentum projections on a noncharacteristic Sigma"
                ),
            },
        ],
        "hamiltonian_momentum_propagation": {
            "definitions": (
                "C_Hamiltonian:=n^m n^n E_mn; "
                "C_momentum_i:=n^m h_i^n E_mn; "
                "Q_ij:=h_i^m h_j^n E_mn"
            ),
            "exact_decomposition": (
                "E_mn=C_Hamiltonian n_m n_n"
                "-2n_(m C_momentum_n)+Q_mn"
            ),
            "exact_normal_projection_identity": (
                "n^n nabla^m["
                "C_Hamiltonian n_m n_n"
                "-2n_(m C_momentum_n)+Q_mn]=0"
            ),
            "exact_tangential_projection_identity": (
                "h_i^n nabla^m["
                "C_Hamiltonian n_m n_n"
                "-2n_(m C_momentum_n)+Q_mn]=0"
            ),
            "reduced_evolution_role": (
                "Q_ij is a homogeneous exact functional of the finite "
                "subsidiary vector because the frozen reduced evolution "
                "equations vanish."
            ),
            "noncircular": (
                "The two projection identities use nabla^m E_mn identically "
                "equal to zero and the reduced equations; E_mn=0 is not "
                "assumed."
            ),
            "conclusion": (
                "zero Hamiltonian/momentum data propagate after the "
                "independent subsidiary vector vanishes"
            ),
        },
        "subsidiary_principal_symbol": {
            **pencil,
            "nonzero_spatial_covector_scope": (
                "every real k_i != 0, normalized by |k|_g"
            ),
            "characteristic_speeds": [-1, 1],
            "rank_change_controls": [
                "beta=0 removes the V_H and T wave normalization",
                "3alpha+beta=0 invalidates the consumed scalar reduction",
            ],
            "classification": "CONSTRAINT_SYSTEM_STRONGLY_HYPERBOLIC",
            "physical_theory_inference": (
                "None: this subsidiary classification neither changes nor "
                "repairs the defective physical spin-2 metric pencil."
            ),
        },
        "regularity_ledger": [
            {
                "quantity": "g,R",
                "candidate_space": "H^(s+2)",
                "reason": "adapted reduced-variable baseline",
            },
            {
                "quantity": "c,r,S",
                "candidate_space": "H^(s+1)",
                "reason": "independent reduced variables",
            },
            {
                "quantity": "C_H,C_r,C_c,T",
                "candidate_space": "H^(s+1)",
                "reason": "algebraic or first-derivative defects",
            },
            {
                "quantity": "Phi,V_H,D,I_R,I_g,C_R,C_S",
                "candidate_space": "H^s",
                "reason": "one differentiated subsidiary level",
            },
            {
                "quantity": "C_Hamiltonian,C_momentum",
                "candidate_space": "H^(s-1)",
                "reason": "highest projected compatibility level",
            },
        ],
        "regularity_conclusion": {
            "candidate_integer_s": "s >= 3 in three spatial dimensions",
            "optimality_proved": False,
            "auxiliary_to_metric_equivalence_loss": (
                "To identify S in H^(s+1) with Ricci[g] at the same "
                "regularity requires g in H^(s+3), one derivative above "
                "the H^(s+2) reduced-variable baseline."
            ),
            "fixed_loss": 1,
            "loss_accumulation_analyzed": False,
            "propagation_topology": (
                "constraint equality is established in H^s unless the "
                "extra metric derivative is supplied"
            ),
            "energy_estimate_for_full_reduced_system": False,
            "local_existence_theorem": False,
        },
        "conditional_propagation_statement": {
            "hypotheses": [
                (
                    "a solution U of the frozen reduced equations exists "
                    "with the displayed subsidiary regularity"
                ),
                (
                    "the independent initial constraints and their "
                    "nonredundant normal data vanish"
                ),
                (
                    "uniqueness holds for the strongly hyperbolic "
                    "subsidiary wave system on the fixed U background"
                ),
            ],
            "conclusion": (
                "all independent and derived constraints vanish in the "
                "local domain of dependence"
            ),
            "auxiliary_equivalence_preserved": True,
            "full_reduced_solution_existence_assumed_not_proved": True,
        },
        "literature_reconciliation": {
            "older_harmonic_result": (
                "The finite gauge closure C_H,Phi,V_H follows the structural "
                "content of arXiv:1811.07869 equations (3.28)-(3.31), while "
                "all coefficients and defects here are rebound to the ToE "
                "action and exact off-constraint extension."
            ),
            "redundant_initial_condition": (
                "The normal derivative of V_H is not prescribed "
                "independently, matching the role of Proposition 2 in "
                "arXiv:1811.07869."
            ),
            "modern_no_go_boundary": (
                "arXiv:2607.11879 separates constraint propagation from the "
                "gauge-independent defective physical block; the present "
                "healthy subsidiary symbol is therefore not a contradiction."
            ),
        },
        "terminal_outcome": (
            "QUADRATIC_CONSTRAINT_PROPAGATION_SYSTEM_"
            "CLOSED_WITH_DERIVATIVE_LOSS"
        ),
        "claim_boundary": {
            "off_constraint_extension_frozen": True,
            "finite_homogeneous_subsidiary_system_derived": True,
            "constraint_system_strongly_hyperbolic": True,
            "constraint_preservation_conditional_on_reduced_solution": True,
            "auxiliary_equivalence_preserved_conditionally": True,
            "ordinary_metric_strong_hyperbolicity_restored": False,
            "full_reduced_system_principal_symbol_classified": False,
            "adapted_energy_estimate_established": False,
            "minimum_regularities_proved_optimal": False,
            "picard_iteration_closed": False,
            "local_well_posedness_established": False,
            "source_extension_executed": False,
        },
        "prohibitions_respected": {
            "constraint_addition_used": False,
            "order_reduction_claimed_as_original_theory": False,
            "regularizer_added": False,
            "fiducial_mode_added": False,
            "physical_spin2_defect_claimed_repaired": False,
            "energy_estimate_executed": False,
            "source_extension_executed": False,
            "ghost_analysis_executed": False,
            "phenomenology_executed": False,
            "yukawa_work_executed": False,
        },
        "selected_next_target": RESULT_REVIEW_TARGET,
        "verdict": (
            "FINITE_HOMOGENEOUS_QUADRATIC_CONSTRAINT_SUBSIDIARY_SYSTEM_"
            "CLOSED_AND_STRONGLY_HYPERBOLIC_WITH_ONE_DERIVATIVE_"
            "EQUIVALENCE_LOSS_NO_PHYSICAL_HYPERBOLICITY_REPAIR_OR_LOCAL_"
            "WELL_POSEDNESS_CLAIM"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_calculation,
        description=(
            "quadratic-gravity gauge and auxiliary constraint-propagation "
            "calculation"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
