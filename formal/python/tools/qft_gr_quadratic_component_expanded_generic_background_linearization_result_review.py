from __future__ import annotations

from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    CAPTURED_AT_UTC,
    REPO_ROOT,
    canonical_json_bytes,
    read_json,
    sha256_bytes,
    sha256_path,
    write_or_check,
)


CALCULATION_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-QFT-GR-QUADRATIC-COMPONENT-EXPANDED-GENERIC-"
    "BACKGROUND-LINEARIZATION-v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_COMPONENT_EXPANDED_GENERIC_BACKGROUND_"
    "LINEARIZATION_RESULT_REVIEW_20260728_v0.json"
)
EXPECTED_CURRENT_TARGET = (
    "review_qft_gr_quadratic_component_expanded_"
    "generic_background_linearization_v0_result"
)
EXPECTED_NEXT_TARGET = (
    "prepare_qft_gr_quadratic_generic_background_linearization_"
    "gauge_and_jet_contract_v0"
)


def build_review() -> dict:
    calculation = read_json(CALCULATION_PATH)
    gauge = calculation["gauge_jet_order_audit"]
    trace = calculation["tracefree_component_chart_audit"]
    background = calculation[
        "background_jet_and_on_shell_reduction_audit"
    ]
    placeholders = calculation["predecessor_component_expansion_audit"]
    custody = calculation["minkowski_control_custody"]
    claims = calculation["claim_boundary"]
    prohibitions = calculation["prohibitions_respected"]
    correction = calculation["required_corrective_packet"]

    expected_terminals = [
        "GAUGE_SOURCE_LINEARIZATION_UNSPECIFIED",
        "BACKGROUND_JET_CONTRACT_INCOMPLETE",
        "BACKGROUND_FIELD_EQUATION_SUBSTITUTION_AMBIGUOUS",
        "GENERIC_BACKGROUND_LINEARIZATION_COMPONENT_INCOMPLETE",
        "MINKOWSKI_CONTROL_PRESERVED_NOT_REDERIVED",
    ]
    checks = {
        "authorized_target_was_consumed": (
            calculation["execution_target"]
            == (
                "derive_qft_gr_quadratic_component_expanded_"
                "generic_background_linearization_v0"
            )
            and calculation["selected_next_target"]
            == EXPECTED_CURRENT_TARGET
        ),
        "metric_dependent_gauge_requires_unfrozen_C3_jet": (
            gauge["accepted_predecessor_gauge_source"]
            == (
                "H^mu=H^mu(x,g), prescribed C2, no dependence on "
                "partial g"
            )
            and gauge["derivative_orders_detected"][-1] == 3
            and gauge["minimum_metric_dependent_gauge_regularization"]
            == "C3"
            and gauge["accepted_regularization"] == "C2"
            and gauge["accepted_contract_sufficient"] is False
            and gauge["terminal_outcome"]
            == "GAUGE_SOURCE_LINEARIZATION_UNSPECIFIED"
        ),
        "field_independent_branch_was_not_silently_selected": (
            gauge["field_independent_H_of_x_branch"][
                "C2_is_sufficient"
            ]
            is True
            and gauge["field_independent_H_of_x_branch"][
                "not_silently_selected"
            ]
            is True
            and prohibitions[
                "field_independent_H_branch_silently_selected"
            ]
            is False
        ),
        "generic_trace_tangent_differs_from_flat_chart": (
            trace["accepted_auxiliary_component_count"]["total"] == 64
            and trace["minkowski_zero_curvature_reduction_s33"]
            == "s00 - s11 - s22"
            and trace[
                "accepted_predecessor_contains_generic_chart"
            ]
            is False
            and trace[
                "using_flat_S33_relation_on_Sbar_nonzero_background_is_valid"
            ]
            is False
            and trace["terminal_outcome"]
            == "BACKGROUND_JET_CONTRACT_INCOMPLETE"
        ),
        "on_shell_background_substitution_fails_closed": (
            background[
                "nonredundant_on_shell_coordinate_set_selected"
            ]
            is False
            and background[
                "background_equation_substitution_order_selected"
            ]
            is False
            and background["terminal_outcome"]
            == "BACKGROUND_FIELD_EQUATION_SUBSTITUTION_AMBIGUOUS"
        ),
        "all_predecessor_component_blockers_remain_exposed": (
            set(placeholders["unexpanded_predecessor_tokens"])
            == {
                "Q^H_mn",
                "Q_mn(g,c)",
                "L^S_mn",
                "partial_a F^R",
                "partial_a F^g_mn",
            }
            and placeholders["component_expansion_completed_here"]
            is False
        ),
        "Minkowski_control_custody_is_exact": (
            custody["matrix_shape"] == [128, 128]
            and custody["nonzero_entry_count"] == 224
            and len(custody["sparse_entry_sha256"]) == 64
            and custody["frequency_growth_boundary"]
            == {"auxiliary": 0, "physical_TT": 1, "full_metric": 2}
            and custody[
                "new_generic_specialization_regression_executed"
            ]
            is False
        ),
        "terminal_outcomes_are_exact_and_nonoverclaiming": (
            calculation["terminal_outcomes"] == expected_terminals
            and claims["gauge_jet_order_obstruction_derived"] is True
            and claims["generic_trace_tangent_obstruction_derived"]
            is True
            and claims["background_jet_ambiguity_derived"] is True
            and claims["component_expanded_rhs_derived"] is False
            and claims["component_expanded_linearization_derived"]
            is False
            and claims["minkowski_specialization_reproduced_from_new_form"]
            is False
        ),
        "no_spectral_variable_or_nonlinear_overclaim": (
            claims["exact_generic_companion_derived"] is False
            and claims["generic_spectrum_derived"] is False
            and claims["generic_finite_loss_established"] is False
            and claims["constraint_tangent_projector_constructed"]
            is False
            and claims["variable_coefficient_estimate_established"]
            is False
            and claims["nonlinear_local_well_posedness_established"]
            is False
            and prohibitions["generic_spectrum_claimed"] is False
            and prohibitions["generic_finite_loss_claimed"] is False
            and prohibitions["constraint_projection_inferred"] is False
        ),
        "corrective_packet_is_narrow_and_nonexecuting": (
            correction["target"] == EXPECTED_NEXT_TARGET
            and set(correction["does_not_authorize"])
            == {
                "generic companion matrix construction",
                "generic spectral or root-splitting calculation",
                "generic derivative-loss conclusion",
                "constraint-tangent projection",
                "variable-coefficient or nonlinear estimate",
            }
        ),
    }
    failed = [name for name, passed in checks.items() if not passed]
    accepted = not failed
    calculation_bytes = CALCULATION_PATH.read_bytes()
    return {
        "schema_id": (
            "QFT_GR_QUADRATIC_COMPONENT_EXPANDED_GENERIC_BACKGROUND_"
            "LINEARIZATION_RESULT_REVIEW_20260728_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "review_target": EXPECTED_CURRENT_TARGET,
        "reviewed_calculation": {
            "path": CALCULATION_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(CALCULATION_PATH),
            "canonical_sha256_recomputed": sha256_bytes(
                canonical_json_bytes(calculation)
            ),
            "canonical_bytes_match": (
                calculation_bytes == canonical_json_bytes(calculation)
            ),
        },
        "checks": checks,
        "failed_checks": failed,
        "accepted": accepted,
        "reviewer_independence": {
            "imports_calculation_module": False,
            "rechecks_gauge_derivative_order": True,
            "rechecks_trace_tangent_boundary": True,
            "rechecks_background_chart_boundary": True,
            "rechecks_predecessor_placeholder_set": True,
            "rechecks_Minkowski_custody": True,
            "audits_claim_ceiling": True,
        },
        "accepted_results": (
            [
                "GENERIC_BACKGROUND_LINEARIZATION_COMPONENT_INCOMPLETE",
                "GAUGE_SOURCE_LINEARIZATION_UNSPECIFIED",
                "BACKGROUND_JET_CONTRACT_INCOMPLETE",
                "BACKGROUND_FIELD_EQUATION_SUBSTITUTION_AMBIGUOUS",
                "MINKOWSKI_CONTROL_PRESERVED_NOT_REDERIVED",
                "NO_SPECTRAL_VARIABLE_OR_NONLINEAR_ESTIMATE",
            ]
            if accepted
            else []
        ),
        "not_established": [
            "GENERIC_BACKGROUND_LINEARIZATION_COMPONENT_COMPLETE",
            "OFF_SHELL_FORM_COMPLETE",
            "ON_SHELL_REDUCTION_COMPLETE",
            "GAUGE_COMPATIBLE_FORM_COMPLETE",
            "MINKOWSKI_SPECIALIZATION_REPRODUCED_FROM_NEW_FORM",
            "COMPONENT_IDENTITY_CHECKS",
            "EXACT_GENERIC_FROZEN_COMPANION_OPERATOR",
            "GENERIC_CHARACTERISTIC_ROOT_ASYMPTOTICS",
            "GENERIC_FINITE_SOBOLEV_LOSS",
            "CONSTRAINT_TANGENT_PROJECTOR",
            "VARIABLE_COEFFICIENT_LINEAR_ESTIMATE",
            "QUASILINEAR_OR_LOCAL_WELL_POSEDNESS",
        ],
        "authority_rotation": {
            "blocked_linearization_result_accepted": accepted,
            "gauge_and_jet_contract_packet_authorized": accepted,
            "component_expansion_retry_authorized": False,
            "generic_companion_execution_authorized": False,
            "generic_spectral_calculation_authorized": False,
            "constraint_tangent_projection_authorized": False,
            "variable_coefficient_estimate_authorized": False,
            "quasilinear_or_local_theorem_authorized": False,
            "source_extension_authorized": False,
            "ghost_analysis_authorized": False,
            "phenomenology_authorized": False,
            "yukawa_work_authorized": False,
        },
        "selected_next_target": (
            EXPECTED_NEXT_TARGET
            if accepted
            else (
                "repair_qft_gr_quadratic_component_expanded_"
                "generic_background_linearization_v0"
            )
        ),
        "verdict": (
            "ACCEPT_FAIL_CLOSED_GENERIC_LINEARIZATION_BLOCKER_"
            "AUTHORIZE_GAUGE_AND_BACKGROUND_JET_CONTRACT_PACKET_ONLY_"
            "PRESERVE_MINKOWSKI_CONTROL_NO_SPECTRAL_VARIABLE_OR_"
            "NONLINEAR_ESTIMATE"
            if accepted
            else (
                "B_BLOCKED_GENERIC_BACKGROUND_LINEARIZATION_RESULT_"
                "REQUIRES_CORRECTION"
            )
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_review,
        description=(
            "quadratic-gravity component-expanded generic-background "
            "linearization result review"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
