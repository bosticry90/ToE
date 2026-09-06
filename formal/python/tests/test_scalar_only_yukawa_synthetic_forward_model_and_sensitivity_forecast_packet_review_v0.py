from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    scalar_only_yukawa_synthetic_forward_model_and_sensitivity_forecast_packet_review_v0
    as review,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / review.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_review_regenerates_and_freezes_packet_custody() -> None:
    assert review.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == review.VERDICT
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_packet_artifacts"]
    } == review.PACKET_HASHES


def test_principal_result_blocks_synthetic_execution() -> None:
    report = _report()
    assert report["principal_packet_review_outcome"] == (
        "BLOCKED_SYNTHETIC_NOISE_OR_NUISANCE_CONTRACT"
    )
    assert report["execution_readiness"] == "NOT_READY"
    assert report["scope"]["synthetic_execution_authorized"] is False
    assert report["scope"]["synthetic_execution_performed"] is False


def test_geometry_symmetry_and_real_observation_count_are_reproduced() -> None:
    geometry = _report()["independent_geometry_check"]
    assert geometry["energy_pi_periodic"] is True
    assert geometry["torque_odd"] is True
    assert geometry["only_even_sine_harmonics_nominal"] is True
    assert geometry["n2_n4_n6_nonzero_representative_check"] is True
    observations = _report()["observation_convention_review"]
    assert observations["gap_count"] == 25
    assert observations["harmonic_count"] == 3
    assert observations["real_quadrature_count"] == 2
    assert observations["real_observation_count"] == 150
    assert observations["complex_observation_count_claim"] is False


def test_covariance_is_mathematically_valid_but_numerically_undercontracted() -> None:
    covariance = _report()["covariance_review"]
    assert covariance["real_covariance_dimension"] == 150
    assert covariance["symmetric_positive_definite"] is True
    assert covariance["minimum_gap_correlation_eigenvalue"] > 0
    assert covariance["full_covariance_condition_number"] < 100
    assert covariance["factorization_and_failure_policy_complete"] is False


def test_monte_carlo_resolution_is_bounded_and_not_five_sigma() -> None:
    monte = _report()["monte_carlo_review"]
    assert monte["null_trials"] == 2000
    assert monte["injection_trials"] == 25000
    assert monte["zero_noise_trials"] == 26
    assert monte["total_synthetic_datasets_if_authorized"] == 27026
    assert 0.015 < monte["maximum_injection_binomial_standard_error"] < 0.016
    assert monte["five_sigma_calibration_supported"] is False


def test_exact_multiplicative_nuisance_degeneracy_is_identified() -> None:
    nuisance = _report()["nuisance_identifiability_review"]
    assert nuisance["data_jacobian_degeneracy"] == (
        "TORQUE_CALIBRATION_COLUMN_EQUALS_DENSITY_MASS_SCALE_COLUMN_AT_NOMINAL_POINT"
    )
    assert nuisance["separately_data_identifiable"] is False
    assert nuisance["penalized_fit_finite_due_to_priors"] is True
    assert nuisance["contract_complete"] is False


def test_computational_execution_plan_is_incomplete() -> None:
    plan = _report()["computational_execution_plan_review"]
    assert plan["minimum_outer_profile_fit_count"] == 675000
    assert plan["complete"] is False
    assert len(plan["missing_items"]) == 12
    assert "FAILED_FIT_CLASSIFICATION" in plan["missing_items"]
    assert "WALL_TIME_AND_MEMORY_CAP" in plan["missing_items"]


def test_exact_seven_diagnostics_and_unblock_requirements() -> None:
    report = _report()
    assert report["diagnostics"] == list(review.DIAGNOSTICS)
    assert len(report["unblock_requirements"]) == 7
    assert all(row["satisfied"] is False for row in report["unblock_requirements"])


def test_twenty_two_gates_have_seven_decision_bearing_failures() -> None:
    gates = _report()["review_gates"]
    assert gates["gate_count"] == 22
    assert gates["pass_count"] == 15
    assert gates["failure_count"] == 7
    failed = [row["gate_id"] for row in gates["rows"] if row["status"] == "FAIL"]
    assert len(failed) == 7
    assert "G14_NUISANCE_DATA_IDENTIFIABILITY" in failed
    assert "G16_COMPUTATIONAL_EXECUTION_PLAN" in failed


def test_no_simulation_empirical_result_or_theory_adoption() -> None:
    scope = _report()["scope"]
    allowed_true = {
        "independent_packet_review_executed",
        "geometry_even_harmonics_verified",
        "real_150_observation_count_verified",
        "covariance_mathematical_positive_definiteness_verified",
        "nuisance_degeneracy_identified",
    }
    for key, value in scope.items():
        assert value is (key in allowed_true), key


def test_human_review_records_block_and_next_authority() -> None:
    text = (REPO_ROOT / review.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        review.VERDICT,
        "150 real components",
        "69.2453279",
        "675000",
        "NOT AUTHORIZED",
        review.SELECTED_NEXT_TARGET,
    ):
        assert token in text

