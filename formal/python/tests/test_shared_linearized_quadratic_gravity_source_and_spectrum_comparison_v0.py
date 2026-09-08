from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    shared_linearized_quadratic_gravity_source_and_spectrum_comparison_v0 as execution,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / execution.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_execution_regenerates_exactly_and_consumes_one_authorized_run() -> None:
    assert execution.artifact_bytes() == execution.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == execution.TARGET
    assert report["verdict"] == execution.VERDICT
    assert report["selected_next_target"] == execution.SELECTED_NEXT_TARGET
    assert report["authority"]["authorized_execution_count"] == 1
    assert {row["relative_path"]: row["sha256"] for row in report["authority"]["frozen_review_artifacts"]} == execution.REVIEW_HASHES


def test_background_gate_passed_before_propagator() -> None:
    gate = _report()["background_gate"]
    assert gate["status"] == "PASSED_BEFORE_PROPAGATOR_CONSTRUCTION"
    assert gate["zero_source"] is gate["zero_background_curvature"] is True
    assert gate["zero_zeroth_order_equation"] is gate["zero_linear_tadpole"] is True
    assert gate["cosmological_term_absent"] is True


def test_exact_euler_tensor_and_trace_are_recorded() -> None:
    equation = _report()["exact_field_equation"]
    assert equation["equation"] == "E_mu_nu[g;alpha,beta]=kappa T_mu_nu"
    for phrase in (
        "2 alpha R(R_mu_nu-g_mu_nu R/4)",
        "2 R_mu_rho_nu_sigma R^rho_sigma",
        "Box R_mu_nu",
    ):
        assert phrase in equation["E_mu_nu"]
    assert equation["identity"] == "nabla^mu E_mu_nu=0"
    assert equation["trace"] == "-R+2(3 alpha+beta)Box R=kappa T"


def test_linearized_equation_keeps_alpha_beta_exact() -> None:
    linear = _report()["linearized_field_equation"]
    assert linear["equation"].startswith("(1+beta Box)G^L_mu_nu")
    assert "(2 alpha+beta)" in linear["equation"]
    assert linear["alpha_beta_treated_exactly"] is True
    assert linear["source_conservation"] == "partial_mu T^mu_nu=0"


def test_source_normalization_and_trace_coefficients_are_checked() -> None:
    checks = _report()["independent_algebra_checks"]
    assert checks["source_normalization"]["derived_rhs_sign"] == "POSITIVE"
    assert checks["source_normalization"]["derived_rhs_coefficient"] == "8 pi G/c^4"
    assert checks["trace_coefficients"] == {
        "Einstein_R": -1,
        "alpha_Box_R": 6,
        "beta_Box_R": 2,
        "trace_equation": "-R^L+2(3 alpha+beta) Box R^L=kappa T",
        "passed": True,
    }


def test_complete_projector_operator_is_inverted() -> None:
    operator = _report()["gauge_fixed_operator"]
    for projector in ("P2", "P1", "P0s", "P0w", "P0sw", "P0ws"):
        assert projector in operator["O_inverse"]
    assert operator["complete_longitudinal_sectors_retained"] is True
    assert operator["scalar_block_identity_verified"] is True
    matrix = _report()["independent_algebra_checks"]["scalar_projector_matrix"]
    assert matrix["passed"] is True
    assert matrix["product_01_polynomial"] == ["0", "0"]
    assert matrix["product_10_polynomial"] == ["0", "0"]


def test_saturated_response_has_expected_partial_fractions() -> None:
    response = _report()["conserved_source_saturated_response"]
    assert "P2/(k^2(1-beta k^2))" in response["unfactorized"]
    assert "-P2/(k^2-m2^2)" in response["partial_fraction"]
    assert "+(P0s/2)/(k^2-m0^2)" in response["partial_fraction"]
    assert response["m0_squared"] == "-1/[2(3 alpha+beta)]"
    assert response["m2_squared"] == "1/beta"
    assert response["longitudinal_terms_after_saturation"] == 0


def test_three_mode_rows_separate_ghost_and_tachyon() -> None:
    register = _report()["mode_register"]
    assert register["mode_count"] == register["derived_mode_count"] == 3
    rows = {row["sector_id"]: row for row in register["rows"]}
    assert rows["MASSLESS_SPIN_2"]["residue_sign"] == "POSITIVE_REFERENCE"
    assert rows["MASSIVE_SCALAR"]["residue_sign"].startswith("POSITIVE")
    assert rows["MASSIVE_SCALAR"]["tachyon_condition"] == "3 alpha+beta>0"
    assert rows["MASSIVE_SPIN_2"]["residue_sign"] == "NEGATIVE_GHOSTLIKE"
    assert rows["MASSIVE_SPIN_2"]["tachyon_condition"] == "beta<0"
    assert "RESIDUE SIGN NOT ASSIGNED" in register["binding_degenerate_rule"]


def test_parameter_partitions_treat_absent_modes_as_limits() -> None:
    partitions = {row["domain"]: row["status"] for row in _report()["parameter_partitions"]}
    assert partitions["beta=0"] == "MASSIVE_SPIN_2_ABSENT_INFINITE_MASS_LIMIT"
    assert partitions["Sigma=0"] == "MASSIVE_SCALAR_ABSENT_INFINITE_MASS_LIMIT"
    assert partitions["alpha=beta=0"] == "EINSTEIN_BASELINE"
    assert partitions["2 alpha+beta=0 and beta!=0"].startswith("COINCIDENT_MASSES_ORTHOGONAL")


def test_static_00_response_has_one_third_and_minus_four_thirds() -> None:
    static = _report()["static_green_functions"]
    assert "(T00-T/2)K0" in static["h00_general"]
    assert "(T/6)Km0" in static["h00_general"]
    assert "-(T00-T/3)Km2" in static["h00_general"]
    assert "1+(1/3)exp(-m0 r)-(4/3)exp(-m2 r)" in static["h00_pressureless_point_source"]
    coefficients = _report()["independent_algebra_checks"]["point_mass_projector_coefficients"]
    assert coefficients == {"massless": "1", "scalar": "1/3", "massive_spin_2": "-4/3"}


def test_static_0i_is_derived_from_same_operator_and_has_no_scalar() -> None:
    static = _report()["static_green_functions"]
    assert static["h0i_general"] == "-2 kappa integral[K0-Km2]T_0i d^3x'"
    assert static["scalar_stationary_0i_contribution"] == 0
    assert static["same_operator_and_inverse_used"] is True
    current = _report()["independent_algebra_checks"]["stationary_current_projectors"]
    assert current["P0s_0i"] == 0
    assert current["passed"] is True


def test_ten_derivations_three_findings_and_eleven_outputs_complete() -> None:
    report = _report()
    derivation = report["derivation_stages"]
    assert derivation["stage_count"] == derivation["completed_stage_count"] == 10
    assert all(row["status"] == "COMPLETED" for row in derivation["rows"])
    assert report["mode_findings"]["finding_count"] == 3
    outputs = report["physical_outputs"]
    assert outputs["output_count"] == outputs["produced_output_count"] == 11
    assert all(row["status"] == "PRODUCED" for row in outputs["rows"])


def test_all_ten_controls_pass_shared_path_without_fitting() -> None:
    controls = _report()["shared_path_controls"]
    assert controls["control_count"] == controls["pass_count"] == 10
    assert controls["failure_count"] == 0
    assert all(row["status"] == "PASSED" for row in controls["rows"])
    assert all(row["uses_shared_derivation_path"] is True for row in controls["rows"])
    assert all(row["coefficient_fitting_used"] is False for row in controls["rows"])


def test_literature_is_used_only_after_derivation() -> None:
    oracles = _report()["post_derivation_oracles"]
    assert len(oracles) == 3
    assert all("AGREE_AFTER_CONVENTION_TRANSLATION" in row["comparison"] for row in oracles)


def test_scope_records_calculation_but_forbids_promotion_and_downstream_work() -> None:
    scope = _report()["scope"]
    assert scope["authorized_execution_consumed"] == 1
    for key in (
        "comparison_execution_completed",
        "metric_variation_executed",
        "linearized_field_equation_derived",
        "propagator_or_mode_calculation_executed",
        "pole_or_residue_judgment_made",
        "Green_functions_computed",
        "independent_result_review_required",
    ):
        assert scope[key] is True
    for key in (
        "comparison_action_selected",
        "coefficient_fitting_executed",
        "empirical_constraint_computed",
        "orbital_precession_computed",
        "frame_dragging_reopened",
        "matter_sector_selected",
        "native_gravitational_principle_identified",
        "new_postulate_authorized",
        "master_action_mutation_authorized",
        "authoritative_V2_population_authorized",
    ):
        assert scope[key] is False


def test_human_record_contains_shared_derivation_results_and_stop() -> None:
    text = (REPO_ROOT / execution.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        execution.VERDICT,
        "D4 — Formal Minkowski background gate: passed",
        "(1+\\beta\\Box)G^L_{\\mu\\nu}",
        "m_2^2=\\frac1\\beta",
        "1+\\frac13e^{-m_0r}-\\frac43e^{-m_2r}",
        "scalar does not contribute",
        "10 / 10 PASSED",
        execution.SELECTED_NEXT_TARGET,
    ):
        assert token in text
