from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import scalar_only_quadratic_gravity_viability_and_native_relevance_v0 as execution


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / execution.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _rows(section: str, id_key: str) -> dict[str, dict[str, object]]:
    return {row[id_key]: row for row in _report()[section]["rows"]}


def test_execution_regenerates_exactly_and_preserves_review_custody() -> None:
    assert execution.artifact_bytes() == REPORT_PATH.read_bytes()
    before = {path: _sha256(REPO_ROOT / path) for path in execution.REVIEW_HASHES}
    execution.build_execution()
    after = {path: _sha256(REPO_ROOT / path) for path in execution.REVIEW_HASHES}
    assert before == after == execution.REVIEW_HASHES


def test_exact_single_execution_authority_is_consumed_and_result_review_is_next() -> None:
    report = _report()
    assert report["target"] == execution.TARGET
    assert report["verdict"] == execution.VERDICT
    assert report["principal_outcome"] == execution.PRINCIPAL_OUTCOME
    assert report["status"] == "PENDING_INDEPENDENT_RESULT_REVIEW"
    assert report["authority"]["authorized_execution_count"] == 1
    assert report["authority"]["consumed_execution_count"] == 1
    assert report["selected_next_target"] == execution.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == execution.SELECTED_NEXT_TARGET_KIND


def test_symbolic_auxiliary_legendre_background_and_mass_checks_pass() -> None:
    audit = _report()["symbolic_audit"]
    assert audit["f"] == "R+alpha R^2"
    assert audit["f_R"] == "2*R*alpha + 1"
    assert audit["f_RR"] == "2*alpha"
    assert audit["auxiliary_equation"] == "2*alpha*(R - chi)"
    assert audit["Jordan_potential_U"] == "(Phi - 1)**2/(4*alpha)"
    assert audit["constant_curvature_lhs"] == "-R0"
    assert audit["supplied_background_solution"] == "R0=-4 kappa rho_Lambda"
    assert audit["scalar_mass_squared"] == "-1/(6*alpha)"
    assert all(audit["checks"].values())


def test_metric_and_exact_trace_equations_are_derived_not_imported() -> None:
    field = _report()["field_equation_result"]
    assert field["metric_equation"].startswith("(1+2 alpha R)R_mu_nu")
    assert field["trace_equation"] == "-R+6 alpha Box R=kappa T"
    assert field["imported_from_literature"] is False


def test_all_ten_derivation_stages_complete() -> None:
    stages = _report()["derivation_stages"]
    assert stages["stage_count"] == stages["completed_stage_count"] == 10
    assert all(row["status"] == "COMPLETED" for row in stages["rows"])
    assert {row["stage_id"] for row in stages["rows"]} == {
        f"D{i}_{suffix}"
        for i, suffix in (
            (1, "METRIC_FIELD_EQUATION"),
            (2, "EXACT_TRACE_EQUATION"),
            (3, "AUXILIARY_AND_LEGENDRE_MAP"),
            (4, "JORDAN_FRAME"),
            (5, "EINSTEIN_FRAME"),
            (6, "MINKOWSKI_CONTROL"),
            (7, "VACUUM_CONSTANT_CURVATURE_CONTROL"),
            (8, "SUPPLIED_MATTER_SUPPORTED_BACKGROUND"),
            (9, "TRACE_MATTER_STABILITY_AND_SCREENING"),
            (10, "NATIVE_RELEVANCE_AUDIT"),
        )
    }


def test_all_eight_scalar_tensor_obligations_are_derived_with_domains() -> None:
    obligations = _report()["scalar_tensor_obligations"]
    assert obligations["obligation_count"] == obligations["derived_count"] == 8
    assert all(row["status"] == "DERIVED" for row in obligations["rows"])
    scalar = _report()["scalar_tensor_result"]
    assert scalar["equivalence_domain"] == "alpha!=0"
    assert scalar["alpha_zero_map_status"] == "NONINVERTIBLE_EINSTEIN_LIMIT"
    assert scalar["conformal_domain"] == "Phi>0"
    assert scalar["frame_observable_equivalence_claimed_without_measurement_map"] is False


def test_jordan_and_einstein_frame_scalar_formulas_are_exact() -> None:
    scalar = _report()["scalar_tensor_result"]
    assert scalar["Phi"] == "1+2 alpha chi"
    assert scalar["inverse"] == "chi=(Phi-1)/(2 alpha)"
    assert scalar["U"] == "(Phi-1)^2/(4 alpha)"
    assert scalar["canonical_scalar"] == "varphi=sqrt(3/(2 kappa)) ln Phi"
    assert scalar["matter_metric"] == "g_matter=Phi^-1 gE"
    assert scalar["matter_coupling_function"].startswith("A(varphi)=Phi^-1/2")
    assert scalar["matter_coupling_derivative"] == (
        "d ln A/dvarphi=-sqrt(kappa/6)"
    )
    assert "d2V/dvarphi2=-1/(6 alpha)" in scalar["translated_potential_minimum"]


def test_parameter_strata_are_classified_without_selecting_alpha() -> None:
    parameters = _report()["parameter_results"]
    assert parameters["alpha_negative"].startswith("NON_TACHYONIC_SCALAR")
    assert parameters["alpha_zero"] == (
        "EINSTEIN_COMPARISON_LIMIT_SCALAR_MAP_NONINVERTIBLE"
    )
    assert parameters["alpha_positive"] == "TACHYONIC_SCALAR_ON_MINKOWSKI"
    assert "positive_infinity" in parameters["alpha_to_zero_negative"]
    assert parameters["selected_alpha"] is None


def test_minkowski_control_reproduces_mass_residue_yukawa_and_zero_scalar_0i() -> None:
    backgrounds = _rows("backgrounds", "background_id")
    minkowski = backgrounds["MINKOWSKI_CONTROL"]
    assert minkowski["status"] == "PASSED"
    assert minkowski["curvature"] == "R0=0"
    assert minkowski["Phi0"] == "1"
    assert minkowski["scalar_mass_squared"] == "-1/(6 alpha)>0 for alpha<0"
    observable = _report()["observable_channel_result"]
    assert observable["point_mass_h00"] == (
        "-2GM/(c^2 r)[1+(1/3)exp(-m0 r)]"
    )
    assert observable["scalar_stationary_0i_direct_contribution"] == 0


def test_pure_vacuum_has_no_nonzero_constant_curvature_background() -> None:
    backgrounds = _rows("backgrounds", "background_id")
    vacuum = backgrounds["CONSTANT_CURVATURE_VACUUM"]
    assert vacuum["status"] == "PASSED_EXISTENCE_NEGATIVE_CONTROL"
    assert vacuum["curvature"] == "R0=0 ONLY"
    assert vacuum["nonzero_de_Sitter_or_anti_de_Sitter"] == "NOT_ADMITTED"
    assert vacuum["stability_claim"] == "NO_NONZERO_BACKGROUND_TO_TEST"


def test_supplied_vacuum_energy_background_solves_equation_and_is_conserved() -> None:
    background = _rows("backgrounds", "background_id")[
        "SUPPLIED_VACUUM_ENERGY_BACKGROUND"
    ]
    assert background["status"] == "PASSED_BOUNDED_LINEAR_SCALAR_TEST"
    assert background["source_action"] == (
        "S_rho=(1/c) integral sqrt(-g) rho_Lambda"
    )
    assert background["source"] == "T_mu_nu=rho_Lambda g_mu_nu"
    assert background["conservation"].startswith("nabla_mu T^mu_nu=0")
    assert background["curvature"] == "R0=-4 kappa rho_Lambda"
    assert background["Phi0"] == "1-8 kappa alpha rho_Lambda"
    assert background["tested_domain"] == (
        "alpha<0 and rho_Lambda>=0 implies Phi0>0"
    )
    assert background["scalar_mass_squared"] == "m0^2=-1/(6 alpha)>0"


def test_stability_notions_are_reported_separately_and_bounded() -> None:
    stability = _report()["stability_result"]
    assert stability["background_existence"].startswith("PASSED_FOR_MINKOWSKI")
    assert stability["positive_kinetic_or_residue"].startswith("PASSED_RELATIVE")
    assert stability["no_tachyonic_linear_mode"] == "PASSED_FOR_ALPHA_NEGATIVE"
    assert stability["matter_stability"].startswith("NO_DOLGOV_KAWASAKI_TACHYON")
    assert stability["no_rapid_runaway"].startswith("PASSED_LINEAR")
    assert stability["nonlinear_or_arbitrary_background_stability"] == (
        "NOT_ESTABLISHED"
    )


def test_traceful_matter_sources_scalar_while_classically_traceless_source_does_not() -> None:
    matter = _report()["matter_trace_result"]
    assert matter["source_status"] == "SUPPLIED_COMPARISON_SOURCE_NOT_TOE_MATTER"
    assert matter["exact_trace_equation"] == (
        "(Box+m0^2)R=(kappa/(6 alpha))T"
    )
    assert matter["traceful_nonrelativistic_source"] == "DIRECT_SCALAR_SOURCE"
    assert matter["classically_traceless_source"] == (
        "NO_DIRECT_LINEAR_SCALAR_SOURCE"
    )
    assert matter["Einstein_frame_trace_relation"] == "T_E=Phi^-2 T_J"


def test_screening_result_is_finite_mass_only_in_the_tested_domain() -> None:
    screening = _report()["screening_result"]
    assert screening["principal_finding"] == "FINITE_MASS_SUPPRESSION_ONLY"
    assert screening["static_kernel"] == "exp(-m0 r)/(4 pi r)"
    assert screening["mass_environment_dependence"] == (
        "NONE_IN_EXACT_FIXED_SOURCE_TRACE_OPERATOR"
    )
    assert screening["coupling_environment_dependence"] == "NONE_DERIVED"
    assert screening["intrinsic_chameleon_or_Vainshtein_mechanism_identified"] is False


def test_all_three_native_candidates_fail_all_seven_bridge_fields() -> None:
    native = _report()["native_relevance_result"]
    assert native["candidate_count"] == 3
    assert native["bridge_identified_count"] == 0
    assert native["required_field_count"] == 7
    assert native["principal_finding"] == "NATIVE_RELEVANCE_NOT_IDENTIFIED"
    assert native["separate_seam_packet_triggered"] is False
    for row in native["rows"]:
        assert row["matched_fields"] == []
        assert len(row["failed_fields"]) == 7
        assert row["bridge_status"] == "NOT_IDENTIFIED"


def test_six_work_packages_complete_and_eight_questions_answered() -> None:
    report = _report()
    packages = report["work_packages"]
    questions = report["decision_questions"]
    assert packages["work_package_count"] == packages["completed_count"] == 6
    assert all(row["status"].startswith("COMPLETED") for row in packages["rows"])
    assert questions["question_count"] == questions["answered_count"] == 8
    assert all(row["status"] == "ANSWERED" for row in questions["rows"])


def test_two_axis_result_supports_bounded_viability_but_no_native_relevance() -> None:
    result = _report()["two_axis_result"]
    assert result["comparison_viability"] == (
        "SUPPORTED_IN_BOUNDED_LINEAR_AND_ONE_SUPPLIED_NON_MINKOWSKI_DOMAIN"
    )
    assert result["native_relevance"] == "NOT_IDENTIFIED"
    assert result["branch_adopted"] is False


def test_all_twelve_shared_path_controls_pass() -> None:
    controls = _report()["shared_path_controls"]
    assert controls["control_count"] == controls["pass_count"] == 12
    assert controls["failure_count"] == 0
    assert all(row["status"] == "PASSED" for row in controls["rows"])


def test_scope_records_execution_but_no_branch_theory_or_downstream_adoption() -> None:
    scope = _report()["scope"]
    for key in (
        "comparison_execution_completed",
        "work_packages_completed",
        "decision_questions_answered",
        "metric_field_equation_derived",
        "scalar_tensor_map_derived",
        "Minkowski_control_reproduced",
        "non_Minkowski_background_test_executed",
        "matter_trace_coupling_derived",
        "screening_assessment_executed",
        "native_bridge_audit_executed",
        "independent_result_review_required",
    ):
        assert scope[key] is True, key
    assert scope["authorized_execution_consumed"] == 1
    for key in (
        "beta_zero_adopted",
        "alpha_sign_or_value_adopted",
        "scalar_branch_adopted",
        "native_scalar_bridge_identified",
        "native_gravitational_principle_identified",
        "gravitational_action_selected",
        "matter_sector_selected",
        "empirical_constraint_computed",
        "orbital_transport_executed",
        "frame_dragging_reopened",
        "master_action_mutation_authorized",
    ):
        assert scope[key] is False, key


def test_human_result_exposes_equations_background_screening_bridge_and_stop() -> None:
    text = (REPO_ROOT / execution.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        execution.VERDICT,
        execution.PRINCIPAL_OUTCOME,
        "-R+6\\alpha\\Box R=\\kappa T",
        "2\\alpha(R-\\chi)=0",
        "U(\\Phi)=\\frac{(\\Phi-1)^2}{4\\alpha}",
        "R_0=-4\\kappa\\rho_\\Lambda",
        "FINITE_MASS_SUPPRESSION_ONLY",
        "NO_NATIVE_SCALAR_BRIDGE_IDENTIFIED",
        "6 / 6 COMPLETED",
        "8 / 8 ANSWERED",
        "12 / 12 PASSED",
        execution.SELECTED_NEXT_TARGET,
    ):
        assert token in text
