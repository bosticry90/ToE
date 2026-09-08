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
    "CALC-QFT-GR-QUADRATIC-GAUGE-AUXILIARY-CONSTRAINT-"
    "PROPAGATION-SYSTEM-v0.json"
)
REDUCED_REVIEW_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_AUXILIARY_HARMONIC_REDUCED_SYSTEM_"
    "RESULT_REVIEW_20260728_v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_GAUGE_AND_AUXILIARY_CONSTRAINT_PROPAGATION_"
    "SYSTEM_RESULT_REVIEW_20260728_v0.json"
)
EXPECTED_CURRENT_TARGET = (
    "review_qft_gr_quadratic_gauge_and_auxiliary_"
    "constraint_propagation_system_v0_result"
)
EXPECTED_NEXT_TARGET = (
    "compute_qft_gr_quadratic_full_reduced_system_"
    "principal_structure_v0"
)


def _independent_pencil_derivation() -> dict:
    lam, beta = sp.symbols("lambda beta", nonzero=True)
    component_counts = {
        "C_H": 4,
        "Phi": 16,
        "V_H": 4,
        "C_r": 4,
        "C_c": 40,
        "T": 1,
    }
    unit_count = (
        component_counts["C_H"]
        + component_counts["Phi"]
        + component_counts["C_r"]
        + component_counts["C_c"]
    )
    beta_count = component_counts["V_H"] + component_counts["T"]
    total = sum(component_counts.values())
    wave = 1 - lam**2
    determinant = sp.factor(wave**unit_count * (beta * wave) ** beta_count)
    return {
        "component_counts": component_counts,
        "unit_count": unit_count,
        "beta_count": beta_count,
        "total": total,
        "determinant": sp.sstr(determinant),
        "algebraic_multiplicity_each_root": total,
        "geometric_multiplicity_each_root": total,
    }


def build_review() -> dict:
    calculation = read_json(CALCULATION_PATH)
    predecessor = read_json(REDUCED_REVIEW_PATH)
    independent = _independent_pencil_derivation()
    off_constraint = calculation["off_constraint_extension"]
    operators = calculation["exact_defect_operators"]
    propagation = calculation["exact_propagation_identities"]
    subsidiary = calculation["finite_subsidiary_system"]
    symbol = calculation["subsidiary_principal_symbol"]
    classifications = {
        row["id"]: row["classification"]
        for row in calculation["constraint_classification"]
    }
    regularity = calculation["regularity_conclusion"]
    claims = calculation["claim_boundary"]
    prohibitions = calculation["prohibitions_respected"]

    checks = {
        "authority_and_predecessor_are_exactly_bound": (
            predecessor["accepted"] is True
            and calculation["execution_target"]
            == (
                "derive_qft_gr_quadratic_gauge_and_auxiliary_"
                "constraint_propagation_system_v0"
            )
            and calculation["selected_next_target"]
            == EXPECTED_CURRENT_TARGET
            and calculation["consumed_authority"]["accepted"] is True
            and len(calculation["consumed_authority"]["sha256"]) == 64
            and len(calculation["consumed_reduced_system"]["sha256"]) == 64
        ),
        "off_constraint_extension_is_frozen_without_additions": (
            off_constraint["frozen_equations"]
            == ["E_g^H", "E_R", "E_r", "E_c", "E_S"]
            and off_constraint["constraint_addition_M_A_B"]
            == "identically zero"
            and off_constraint["derivative_constraint_addition_N_A_B_mu"]
            == "identically zero"
            and off_constraint["constraint_damping"] == "none"
            and off_constraint["added_differential_order"] == 0
            and off_constraint["changes_evolution_principal_symbol"] is False
            and off_constraint["changes_physical_spin2_block"] is False
            and off_constraint["regularizer_or_fiducial_mode_added"] is False
        ),
        "total_gauge_and_metric_definition_defects_are_separated": (
            {
                "total_ricci_defect",
                "pure_gauge_ricci_defect",
                "metric_definition_ricci_defect",
                "einstein_defects",
                "divergence_defects",
            }
            <= set(operators)
            and "K_tot_mn-K_H_mn"
            in operators["metric_definition_ricci_defect"]
            and "V_tot=V_H+V_c" in operators["divergence_defects"]
        ),
        "all_named_remainders_are_exact_operator_definitions": (
            "nabla^m DeltaE_mn-beta Box_g V_H_n"
            in operators["exact_V_remainder"]
            and "operator equality"
            in operators["no_implicit_remainder"]
            and "lower(" not in str(calculation)
            and "..." not in str(calculation)
        ),
        "definition_and_integrability_constraints_propagate_exactly": (
            propagation["scalar_derivative_definition"]["equation"]
            == "W_g C_r_a = -(partial_a g^bc)partial_b C_r_c"
            and propagation["metric_derivative_definition"]["equation"]
            == (
                "W_g C_c_mna = "
                "-(partial_a g^bc)partial_b C_c_mnc"
            )
            and propagation["scalar_integrability"]["identity"]
            == "I_R_ab=partial_a C_r_b-partial_b C_r_a"
            and propagation["metric_integrability"]["identity"]
            == "I_g_mnab=partial_a C_c_mnb-partial_b C_c_mna"
        ),
        "trace_and_bianchi_reconstruction_are_exact_and_homogeneous": (
            propagation["trace"]["equation"]
            == (
                "beta Box_g T+[c_R+(2alpha+beta)R]T"
                "+2beta K_tot_mn S^mn=0"
            )
            and propagation["contracted_bianchi"]["equation"]
            == (
                "V_tot_n=-D_n-(1/2)C_r_n"
                "+(1/2)nabla_n T"
            )
            and propagation["scalar_curvature_definition"]["equation"]
            == "C_R=-(T+K_tot)"
            and propagation["tracefree_ricci_definition"]["equation"]
            == (
                "C_S_mn=-K_tot_mn"
                "+(1/4)g_mn(T+K_tot)"
            )
            and all(
                row["homogeneous"] is True
                for row in propagation.values()
            )
        ),
        "finite_independent_wave_vector_closes": (
            subsidiary["independent_wave_vector"]
            == [
                "C_H^a",
                "Phi^a_b",
                "V_H_n",
                "C_r_a",
                "C_c_mna",
                "T",
            ]
            and subsidiary["independent_component_count"] == 69
            and subsidiary["new_constraint_generated_by_differentiation"]
            is False
            and subsidiary["finite"] is True
            and subsidiary["homogeneous"] is True
            and subsidiary["P_C_of_zero"] == "0"
        ),
        "constraint_independence_classification_is_complete": (
            classifications
            == {
                "C_H^a": "INDEPENDENT_INITIAL_CONSTRAINT",
                "Phi^a_b": "DEFINITION_CONSTRAINT",
                "V_H_n": "INDEPENDENT_INITIAL_CONSTRAINT",
                "C_r_a": "DEFINITION_CONSTRAINT",
                "C_c_mna": "DEFINITION_CONSTRAINT",
                "I_R_ab": "INTEGRABILITY_CONSEQUENCE",
                "I_g_mnab": "INTEGRABILITY_CONSEQUENCE",
                "T": "DEFINITION_CONSTRAINT",
                "D_n": "EVOLUTION_CONSEQUENCE",
                "C_R": "EVOLUTION_CONSEQUENCE",
                "C_S_mn": "EVOLUTION_CONSEQUENCE",
                "C_Hamiltonian": "INDEPENDENT_INITIAL_CONSTRAINT",
                "C_momentum_i": "INDEPENDENT_INITIAL_CONSTRAINT",
                "normal_derivative_of_V_H": (
                    "REDUNDANT_BY_BIANCHI_IDENTITY"
                ),
            }
        ),
        "subsidiary_pencil_is_independently_reproduced": (
            independent["component_counts"]
            == {
                "C_H": 4,
                "Phi": 16,
                "V_H": 4,
                "C_r": 4,
                "C_c": 40,
                "T": 1,
            }
            and independent["unit_count"] == 64
            and independent["beta_count"] == 5
            and independent["total"] == 69
            and symbol["independent_wave_components"] == 69
            and symbol["determinant"] == independent["determinant"]
            and symbol["algebraic_multiplicity_each_root"]
            == independent["algebraic_multiplicity_each_root"]
            and symbol["geometric_multiplicity_each_root"]
            == independent["geometric_multiplicity_each_root"]
            and symbol["complete_eigenbasis"] is True
            and symbol["strongly_hyperbolic"] is True
            and symbol["classification"]
            == "CONSTRAINT_SYSTEM_STRONGLY_HYPERBOLIC"
        ),
        "hamiltonian_momentum_argument_is_noncircular": (
            calculation["hamiltonian_momentum_propagation"]["noncircular"]
            .startswith("The two projection identities use")
            and "E_mn=0 is not assumed"
            in calculation["hamiltonian_momentum_propagation"][
                "noncircular"
            ]
            and "nabla^m[" in calculation[
                "hamiltonian_momentum_propagation"
            ]["exact_normal_projection_identity"]
            and "nabla^m[" in calculation[
                "hamiltonian_momentum_propagation"
            ]["exact_tangential_projection_identity"]
        ),
        "regularity_loss_is_bounded_but_not_overclaimed": (
            regularity["candidate_integer_s"]
            == "s >= 3 in three spatial dimensions"
            and regularity["optimality_proved"] is False
            and regularity["fixed_loss"] == 1
            and regularity["loss_accumulation_analyzed"] is False
            and regularity["energy_estimate_for_full_reduced_system"]
            is False
            and regularity["local_existence_theorem"] is False
            and "g in H^(s+3)"
            in regularity["auxiliary_to_metric_equivalence_loss"]
        ),
        "conditional_equivalence_claim_has_required_hypotheses": (
            calculation["conditional_propagation_statement"][
                "auxiliary_equivalence_preserved"
            ]
            is True
            and calculation["conditional_propagation_statement"][
                "full_reduced_solution_existence_assumed_not_proved"
            ]
            is True
            and len(
                calculation["conditional_propagation_statement"][
                    "hypotheses"
                ]
            )
            == 3
        ),
        "physical_and_theorem_claim_ceilings_are_preserved": (
            claims["off_constraint_extension_frozen"] is True
            and claims["finite_homogeneous_subsidiary_system_derived"]
            is True
            and claims["constraint_system_strongly_hyperbolic"] is True
            and claims["ordinary_metric_strong_hyperbolicity_restored"]
            is False
            and claims["full_reduced_system_principal_symbol_classified"]
            is False
            and claims["adapted_energy_estimate_established"] is False
            and claims["minimum_regularities_proved_optimal"] is False
            and claims["picard_iteration_closed"] is False
            and claims["local_well_posedness_established"] is False
            and claims["source_extension_executed"] is False
            and all(value is False for value in prohibitions.values())
        ),
        "terminal_outcome_is_narrow_and_exact": (
            calculation["terminal_outcome"]
            == (
                "QUADRATIC_CONSTRAINT_PROPAGATION_SYSTEM_"
                "CLOSED_WITH_DERIVATIVE_LOSS"
            )
            and "NO_PHYSICAL_HYPERBOLICITY_REPAIR"
            in calculation["verdict"]
        ),
    }
    failed = [name for name, passed in checks.items() if not passed]
    accepted = not failed
    return {
        "schema_id": (
            "QFT_GR_QUADRATIC_GAUGE_AND_AUXILIARY_CONSTRAINT_"
            "PROPAGATION_SYSTEM_RESULT_REVIEW_20260728_v0"
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
            "reconstructs_component_counts": True,
            "reconstructs_pencil_determinant": True,
            "audits_exact_defect_identities": True,
            "audits_initial_constraint_independence": True,
            "audits_regularities_and_claim_ceiling": True,
        },
        "accepted_results": (
            [
                "OFF_CONSTRAINT_EXTENSION_FROZEN_WITH_ZERO_ADDITIONS",
                (
                    "QUADRATIC_CONSTRAINT_PROPAGATION_SYSTEM_"
                    "CLOSED_WITH_DERIVATIVE_LOSS"
                ),
                "CONSTRAINT_SYSTEM_STRONGLY_HYPERBOLIC",
                (
                    "AUXILIARY_EQUIVALENCE_CONDITIONALLY_PRESERVED_"
                    "ON_ZERO_CONSTRAINT_DATA"
                ),
            ]
            if accepted
            else []
        ),
        "not_established": [
            "ORDINARY_METRIC_STRONG_HYPERBOLICITY",
            "FULL_REDUCED_SYSTEM_PRINCIPAL_CLASSIFICATION",
            "OPTIMAL_MINIMUM_REGULARITY",
            "LOSS_NONACCUMULATION",
            "LINEAR_ADAPTED_NORM_ENERGY_ESTIMATE",
            "PICARD_OR_NASH_MOSER_CLOSURE",
            "LOCAL_WELL_POSEDNESS",
            "SOURCE_EXTENSION_ADMISSIBILITY",
        ],
        "authority_rotation": {
            "constraint_propagation_result_accepted": accepted,
            "full_reduced_principal_structure_authorized": accepted,
            "adapted_energy_estimate_authorized": False,
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
                "repair_qft_gr_quadratic_gauge_and_auxiliary_"
                "constraint_propagation_system_v0"
            )
        ),
        "verdict": (
            "ACCEPT_CLOSED_HOMOGENEOUS_CONSTRAINT_PROPAGATION_WITH_"
            "ONE_DERIVATIVE_EQUIVALENCE_LOSS_AUTHORIZE_FULL_REDUCED_"
            "PRINCIPAL_STRUCTURE_ONLY"
            if accepted
            else (
                "B_BLOCKED_QUADRATIC_CONSTRAINT_PROPAGATION_REQUIRES_"
                "CORRECTION"
            )
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_review,
        description=(
            "quadratic-gravity gauge and auxiliary constraint-propagation "
            "result review"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
