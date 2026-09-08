from __future__ import annotations

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


AUTHORITY_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_EXACT_GENERIC_FROZEN_COMPANION_OPERATOR_"
    "RESULT_REVIEW_20260728_v0.json"
)
REDUCED_SYSTEM_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-QFT-GR-QUADRATIC-AUXILIARY-HARMONIC-REDUCED-SYSTEM-v0.json"
)
MINKOWSKI_CONTROL_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-QFT-GR-QUADRATIC-EXACT-GENERIC-FROZEN-COMPANION-"
    "OPERATOR-v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-QFT-GR-QUADRATIC-COMPONENT-EXPANDED-GENERIC-"
    "BACKGROUND-LINEARIZATION-v0.json"
)
CURRENT_TARGET = (
    "derive_qft_gr_quadratic_component_expanded_"
    "generic_background_linearization_v0"
)
RESULT_REVIEW_TARGET = (
    "review_qft_gr_quadratic_component_expanded_"
    "generic_background_linearization_v0_result"
)
PROPOSED_PREREQUISITE_TARGET = (
    "prepare_qft_gr_quadratic_generic_background_linearization_"
    "gauge_and_jet_contract_v0"
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


def gauge_jet_order_audit() -> dict:
    """Derive the minimum H jet needed by the differentiated metric block."""

    epsilon, x, g = sp.symbols("epsilon x g")
    c, dc = sp.symbols("c dc")
    h, delta_c, delta_dc = sp.symbols("h delta_c delta_dc")
    H = sp.Function("H")

    # A representative component of partial_n H^mu(x,g) in F_g.
    first_total = sp.diff(H(x, g), x) + sp.diff(H(x, g), g) * c
    # F_c contains one further coordinate derivative.
    second_total = (
        sp.diff(first_total, x)
        + sp.diff(first_total, g) * c
        + sp.diff(first_total, c) * dc
    )
    # Linearizing a metric-dependent H varies g, c=partial g, and partial c.
    perturbed = second_total.subs(
        {
            g: g + epsilon * h,
            c: c + epsilon * delta_c,
            dc: dc + epsilon * delta_dc,
        }
    )
    linearized_second_total = sp.diff(perturbed, epsilon).subs(epsilon, 0)
    derivative_orders = sorted(
        {
            int(sum(count for _, count in derivative.variable_count))
            for derivative in linearized_second_total.atoms(sp.Derivative)
        }
    )
    if derivative_orders[-1] != 3:
        raise QuadraticHyperbolicityError(
            "metric-dependent gauge audit did not expose the third H jet"
        )

    return {
        "accepted_predecessor_gauge_source": (
            "H^mu=H^mu(x,g), prescribed C2, no dependence on partial g"
        ),
        "metric_equation_dependency": (
            "F_g contains partial_n H^mu = H^mu_,x^n "
            "+H^mu_,g_pq c_pqn"
        ),
        "metric_derivative_equation_dependency": (
            "F_c=partial_a F_g-(partial_a g^bc)partial_b c_mnc "
            "contains partial_a partial_n H^mu"
        ),
        "linearization_dependency": (
            "delta(partial_a partial_n H^mu(x,g)) contains "
            "H_xxg delta g, H_xgg c delta g, H_ggg c c delta g, "
            "and H_xg/H_gg delta c terms"
        ),
        "symbolic_representative": sp.sstr(
            sp.expand(linearized_second_total)
        ),
        "derivative_orders_detected": derivative_orders,
        "minimum_metric_dependent_gauge_regularization": "C3",
        "accepted_regularization": "C2",
        "accepted_contract_sufficient": False,
        "field_independent_H_of_x_branch": {
            "C2_is_sufficient": True,
            "status": (
                "AVAILABLE_ONLY_AFTER_EXPLICIT_SCIENTIFIC_CONTRACT_FREEZE"
            ),
            "not_silently_selected": True,
            "reason": (
                "The complete frozen subprincipal operator is the target; "
                "narrowing its gauge-source dependence changes coefficients "
                "that the calculation is meant to classify."
            ),
        },
        "terminal_outcome": "GAUGE_SOURCE_LINEARIZATION_UNSPECIFIED",
    }


def tracefree_chart_audit() -> dict:
    """Derive the generic tangent trace relation and its flat reduction."""

    h00, h11, h22, h33 = sp.symbols("h00 h11 h22 h33")
    s00, s11, s22, s33 = sp.symbols("s00 s11 s22 s33")
    S00, S11, S22, S33 = sp.symbols("Sbar00 Sbar11 Sbar22 Sbar33")
    # Diagonal representative of delta(g^mn S_mn)=0 at eta.  The complete
    # component formula below also records off-diagonal contractions.
    delta_inverse_contraction = -h00 * S00 - h11 * S11 - h22 * S22 - h33 * S33
    trace_variation = (
        -s00 + s11 + s22 + s33 + delta_inverse_contraction
    )
    solved_s33 = sp.solve(trace_variation, s33)[0]
    flat_s33 = sp.simplify(
        solved_s33.subs({S00: 0, S11: 0, S22: 0, S33: 0})
    )
    if flat_s33 != s00 - s11 - s22:
        raise QuadraticHyperbolicityError(
            "flat trace tangent does not reproduce the accepted chart"
        )

    return {
        "accepted_auxiliary_component_count": {
            "g": 10,
            "c": 40,
            "R": 1,
            "r": 4,
            "S_tracefree": 9,
            "total": 64,
        },
        "covariant_linearized_trace": (
            "delta C_tr = gbar^mn delta S_mn "
            "-gbar^mp gbar^nq Sbar_mn delta g_pq = 0"
        ),
        "orthonormal_diagonal_representative_s33": sp.sstr(solved_s33),
        "minkowski_zero_curvature_reduction_s33": sp.sstr(flat_s33),
        "generic_difference_from_minkowski_chart": sp.sstr(
            sp.expand(solved_s33 - flat_s33)
        ),
        "required_generic_chart_data": [
            "the dependent S component or an explicit rank-nine projector",
            "a nonvanishing denominator domain for the selected chart",
            "metric dependence of the rank-nine inclusion map",
            "first derivatives of that inclusion map in F_c and constraints",
            "its tangent action on delta g and delta S",
        ],
        "accepted_predecessor_contains_generic_chart": False,
        "using_flat_S33_relation_on_Sbar_nonzero_background_is_valid": False,
        "terminal_outcome": "BACKGROUND_JET_CONTRACT_INCOMPLETE",
    }


def background_jet_audit() -> dict:
    return {
        "off_shell_generic_jet_required": [
            "gbar_mn and inverse gbar^mn",
            "cbar_mna and partial_b cbar_mna",
            "Rbar and partial_a Rbar",
            "rbar_a and partial_b rbar_a",
            "Sbar_mn and partial_a Sbar_mn",
            "second reduced-field jet partial_a partial_b Ubar",
            "prescribed H jet at the regularity selected by the gauge branch",
        ],
        "linearized_wave_coefficient_term": (
            "delta(g^ab) partial_a partial_b Ubar"
        ),
        "off_shell_residual_contract": (
            "L_Ubar(delta U) = -E_reduced[Ubar] must retain all 64 "
            "background residual components"
        ),
        "on_shell_required_relations": [
            "all reduced evolution residuals vanish",
            "cbar_mna=partial_a gbar_mn",
            "rbar_a=partial_a Rbar",
            "Rbar=gbar^mn Ricci_mn[gbar]",
            (
                "Sbar_mn=Ricci_mn[gbar]"
                "-(1/4)gbar_mn Rbar"
            ),
            "trace and divergence constraints vanish",
            "definition and integrability constraints vanish",
            "Hamiltonian and momentum projections vanish",
        ],
        "gauge_compatible_required_relations": [
            "Gammabar^mu=Hbar^mu",
            "partial_a Gammabar^mu=partial_a Hbar^mu",
            (
                "partial_a partial_b Gammabar^mu="
                "partial_a partial_b Hbar^mu"
            ),
        ],
        "nonredundant_on_shell_coordinate_set_selected": False,
        "background_equation_substitution_order_selected": False,
        "why_order_matters": (
            "Eliminating contracted second derivatives with evolution "
            "equations before or after solving definition, trace, and gauge "
            "relations changes the displayed independent coefficient set. "
            "No accepted chart fixes that choice."
        ),
        "terminal_outcome": (
            "BACKGROUND_FIELD_EQUATION_SUBSTITUTION_AMBIGUOUS"
        ),
    }


def predecessor_placeholder_audit(reduced: dict) -> dict:
    serialized = canonical_json_bytes(
        {
            "exact_operator_definitions": reduced[
                "exact_operator_definitions"
            ],
            "closed_second_order_system": reduced[
                "closed_second_order_system"
            ],
        }
    ).decode("utf-8")
    expected = (
        "Q^H_mn",
        "Q_mn(g,c)",
        "L^S_mn",
        "partial_a F^R",
        "partial_a F^g_mn",
    )
    found = [token for token in expected if token in serialized]
    if found != list(expected):
        raise QuadraticHyperbolicityError(
            "accepted predecessor placeholder set changed"
        )
    return {
        "unexpanded_predecessor_tokens": found,
        "component_expansion_completed_here": False,
        "reason": (
            "Expanding these expressions before freezing the missing gauge "
            "and trace-tangent contracts would select scientifically "
            "material subprincipal coefficients without authority."
        ),
    }


def minkowski_control_custody(control: dict) -> dict:
    minkowski = control["exact_minkowski_control"]
    entries = minkowski["sparse_entries"]
    entry_hash = sha256_bytes(canonical_json_bytes(entries))
    if minkowski["matrix_shape"] != [128, 128]:
        raise QuadraticHyperbolicityError(
            "accepted Minkowski control shape changed"
        )
    if minkowski["nonzero_entry_count"] != 224 or len(entries) != 224:
        raise QuadraticHyperbolicityError(
            "accepted Minkowski sparse count changed"
        )
    if entry_hash != minkowski["sparse_entry_sha256"]:
        raise QuadraticHyperbolicityError(
            "accepted Minkowski sparse-entry hash changed"
        )
    return {
        "classification": (
            "ACCEPTED_MINKOWSKI_CONTROL_PRESERVED_NOT_REDERIVED"
        ),
        "matrix_shape": minkowski["matrix_shape"],
        "nonzero_entry_count": minkowski["nonzero_entry_count"],
        "sparse_entry_sha256": entry_hash,
        "variable_order": minkowski["variable_order"],
        "frequency_growth_boundary": {
            "auxiliary": 0,
            "physical_TT": 1,
            "full_metric": 2,
        },
        "new_generic_specialization_regression_executed": False,
        "why_not": (
            "No generic component linearization was accepted, so claiming "
            "a new specialization regression would be circular."
        ),
    }


def build_calculation() -> dict:
    authority = read_json(AUTHORITY_PATH)
    reduced = read_json(REDUCED_SYSTEM_PATH)
    minkowski = read_json(MINKOWSKI_CONTROL_PATH)
    if authority["accepted"] is not True:
        raise QuadraticHyperbolicityError(
            "generic frozen companion result review was not accepted"
        )
    if authority["selected_next_target"] != CURRENT_TARGET:
        raise QuadraticHyperbolicityError(
            "component-expanded linearization authority mismatch"
        )
    if authority["authority_rotation"][
        "component_expanded_background_linearization_authorized"
    ] is not True:
        raise QuadraticHyperbolicityError(
            "component-expanded linearization is not authorized"
        )

    gauge = gauge_jet_order_audit()
    trace = tracefree_chart_audit()
    background = background_jet_audit()
    placeholders = predecessor_placeholder_audit(reduced)
    custody = minkowski_control_custody(minkowski)

    return {
        "schema_id": (
            "CALC_QFT_GR_QUADRATIC_COMPONENT_EXPANDED_GENERIC_"
            "BACKGROUND_LINEARIZATION_v0"
        ),
        "calculation_id": (
            "CALC-QFT-GR-QUADRATIC-COMPONENT-EXPANDED-GENERIC-"
            "BACKGROUND-LINEARIZATION-v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "execution_target": CURRENT_TARGET,
        "consumed_authority": {
            "path": AUTHORITY_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(AUTHORITY_PATH),
            "accepted_results": authority["accepted_results"],
        },
        "consumed_reduced_system": {
            "path": REDUCED_SYSTEM_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(REDUCED_SYSTEM_PATH),
        },
        "consumed_minkowski_control": {
            "path": MINKOWSKI_CONTROL_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(MINKOWSKI_CONTROL_PATH),
        },
        "gauge_jet_order_audit": gauge,
        "tracefree_component_chart_audit": trace,
        "background_jet_and_on_shell_reduction_audit": background,
        "predecessor_component_expansion_audit": placeholders,
        "minkowski_control_custody": custody,
        "identity_check_boundary": {
            "linearized_contracted_bianchi_component_check": "NOT_EXECUTED",
            "trace_and_tracefree_recombination_check": "NOT_EXECUTED",
            "divergence_of_spin2_equation_check": "NOT_EXECUTED",
            "gauge_constraint_propagation_check": (
                "PRESERVED_FROM_ACCEPTED_PREDECESSOR_NOT_REPROVED"
            ),
            "definition_and_integrability_checks": (
                "PRESERVED_FROM_ACCEPTED_PREDECESSOR_NOT_REPROVED"
            ),
            "reason": (
                "The exact component linearization on which these checks "
                "operate is blocked. Passing an identity check against an "
                "unfrozen gauge or trace chart would be meaningless."
            ),
        },
        "terminal_outcomes": [
            "GAUGE_SOURCE_LINEARIZATION_UNSPECIFIED",
            "BACKGROUND_JET_CONTRACT_INCOMPLETE",
            "BACKGROUND_FIELD_EQUATION_SUBSTITUTION_AMBIGUOUS",
            "GENERIC_BACKGROUND_LINEARIZATION_COMPONENT_INCOMPLETE",
            "MINKOWSKI_CONTROL_PRESERVED_NOT_REDERIVED",
        ],
        "claim_boundary": {
            "gauge_jet_order_obstruction_derived": True,
            "generic_trace_tangent_obstruction_derived": True,
            "background_jet_ambiguity_derived": True,
            "component_expanded_rhs_derived": False,
            "component_expanded_linearization_derived": False,
            "off_shell_form_complete": False,
            "on_shell_reduction_complete": False,
            "gauge_compatible_form_complete": False,
            "minkowski_specialization_reproduced_from_new_form": False,
            "component_identity_checks_passed": False,
            "exact_generic_companion_derived": False,
            "generic_spectrum_derived": False,
            "generic_finite_loss_established": False,
            "constraint_tangent_projector_constructed": False,
            "variable_coefficient_estimate_established": False,
            "nonlinear_local_well_posedness_established": False,
        },
        "prohibitions_respected": {
            "C3_metric_dependent_H_jet_invented": False,
            "field_independent_H_branch_silently_selected": False,
            "flat_tracefree_chart_used_generically": False,
            "on_shell_background_chart_invented": False,
            "implicit_remainder_called_component_expansion": False,
            "minkowski_called_generic": False,
            "generic_spectrum_claimed": False,
            "generic_finite_loss_claimed": False,
            "constraint_projection_inferred": False,
            "variable_or_nonlinear_estimate_claimed": False,
            "source_extension_executed": False,
            "ghost_analysis_executed": False,
            "phenomenology_executed": False,
            "yukawa_work_executed": False,
        },
        "required_corrective_packet": {
            "target": PROPOSED_PREREQUISITE_TARGET,
            "must_freeze": [
                (
                    "choose field-independent H(x) C2 or upgrade and "
                    "componentize metric-dependent H(x,g) through C3"
                ),
                (
                    "choose a generic rank-nine tracefree S projector and "
                    "its tangent/derivative maps"
                ),
                (
                    "choose independent off-shell, on-shell, and "
                    "gauge-compatible background jet coordinates"
                ),
                (
                    "freeze the order of background field-equation and "
                    "constraint substitutions"
                ),
                (
                    "freeze component identity checks and the third "
                    "perturbation jet needed by the Bianchi audit"
                ),
            ],
            "does_not_authorize": [
                "generic companion matrix construction",
                "generic spectral or root-splitting calculation",
                "generic derivative-loss conclusion",
                "constraint-tangent projection",
                "variable-coefficient or nonlinear estimate",
            ],
        },
        "selected_next_target": RESULT_REVIEW_TARGET,
        "verdict": (
            "GENERIC_COMPONENT_LINEARIZATION_BLOCKED_BY_UNFROZEN_"
            "METRIC_DEPENDENT_GAUGE_C3_JET_GENERIC_TRACEFREE_TANGENT_"
            "CHART_AND_ON_SHELL_BACKGROUND_SUBSTITUTION_ORDER_"
            "MINKOWSKI_CONTROL_PRESERVED_NO_SPECTRAL_VARIABLE_OR_"
            "NONLINEAR_CLAIM"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_calculation,
        description=(
            "quadratic-gravity component-expanded generic-background "
            "linearization calculation"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
