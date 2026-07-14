from __future__ import annotations

from formal.python.tools import dirac_maxwell_full_zero_mode_reduction_with_transverse_fields_result_review as review


def test_full_zero_mode_review_artifact_is_current() -> None:
    report = review.build_review_report()
    assert review.REVIEW_REPORT_PATH.read_bytes() == review.canonical_json_bytes(report)


def test_independent_audit_reconstructs_Maxwell_and_gamma_structure() -> None:
    audit = review.independent_reduction_audit()
    assert audit["Maxwell_decomposition_passed"] is True
    assert audit["lagrangian_coefficients"] == {
        "F01_squared": 0.5,
        "phi2_time_squared": 0.5,
        "phi2_space_squared": -0.5,
        "phi3_time_squared": 0.5,
        "phi3_space_squared": -0.5,
    }
    assert audit["gamma_longitudinal_mixing_norm"] == "0.0e+00"
    assert float(audit["gamma_transverse_min_mixing_norm"]) > 0


def test_independent_audit_reconstructs_wave_exchange_and_stress_signs() -> None:
    audit = review.independent_reduction_audit()
    assert audit["scalar_wave_signs"]["Euler_Lagrange_equation"] == "Box phi_I=-mu_0 J^I=mu_0 J_I"
    assert audit["exchange_sum_zero"] is True
    assert audit["stress_tensor_descendant_coefficients"] == {
        "gradient_outer_product": 1,
        "metric_trace": "-1/2",
        "matches_parent_ab_components": True,
    }


def test_review_accepts_analytic_repair_and_all_decisions() -> None:
    report = review.build_review_report()
    assert report["accepted"] is True
    assert report["verdict"] == "ACCEPT"
    assert report["passed_decision_count"] == report["decision_count"] == 16
    assert report["authority_rotation"]["full_zero_mode_analytic_repair_accepted"] is True
    assert report["authority_rotation"]["pure_1p1_truncation_rehabilitated"] is False
    assert report["authority_rotation"]["transverse_mode_decoupling_claimed"] is False


def test_review_authorizes_only_numerical_guardrail_preparation() -> None:
    report = review.build_review_report()
    authority = report["authority_rotation"]
    assert report["selected_next_target"] == review.ACCEPTED_TARGET
    assert authority["numerical_guardrail_preparation_authorized"] is True
    assert authority["numerical_guardrail_accepted"] is False
    assert authority["execution_authorized"] is False


def test_preparation_custody_and_prompt_are_exact() -> None:
    report = review.build_review_report()
    assert report["preparation_custody"]["passed"] is True
    assert review.sha256_path(review.REPO_ROOT / review.PROMPT_RELATIVE_PATH) == review.PROMPT_SHA256
