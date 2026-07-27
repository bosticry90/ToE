from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_packet_v0
    as packet,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / packet.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_packet_regenerates_and_freezes_selection_authority() -> None:
    assert packet.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == packet.TARGET
    assert report["verdict"] == packet.VERDICT
    assert report["selected_next_target"] == packet.SELECTED_NEXT_TARGET
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_response_selection_artifacts"]
    } == packet.AUTHORITY_HASHES


def test_stage_a_contains_no_stochastic_contract() -> None:
    boundary = _report()["stage_a_boundary"]
    assert boundary["gaussian_noise"] == "NONE"
    assert boundary["covariance"] == "NONE"
    assert boundary["monte_carlo_trials"] == "NONE"
    assert boundary["profile_likelihood"] == "NONE"
    assert boundary["sensitivity_forecast"] == "NONE"
    assert boundary["execution"] == "NOT_AUTHORIZED"


def test_harmonic_convention_and_real_vector_are_exact() -> None:
    harmonic = _report()["harmonic_contract"]
    assert harmonic["coefficient"] == "c_n=(1/(2*pi))*integral(tau*exp(-i*n*theta),theta=0..2*pi)"
    assert harmonic["a_n_relation"] == "a_n=2*Re(c_n)"
    assert harmonic["b_n_relation"] == "b_n=-2*Im(c_n)"
    assert harmonic["production_sample_count"] == 256
    assert harmonic["retained_harmonics"] == [2, 4, 6]
    assert harmonic["real_vector_length"] == 150
    assert harmonic["ordering"] == "GAP_MAJOR_2RE_2IM_4RE_4IM_6RE_6IM"


def test_one_production_kernel_and_two_torque_cross_checks_are_frozen() -> None:
    production = _report()["production_path"]
    assert production["shared_function_count"] == 6
    assert production["production_torque"] == "ANALYTIC_NEGATIVE_ENERGY_DERIVATIVE"
    assert production["cross_checks"] == [
        "DIRECT_PAIR_FORCE_LEVER_ARM",
        "FIVE_POINT_CENTRAL_ENERGY_DERIVATIVE",
    ]
    assert production["benchmark_only_kernel_allowed"] is False


def test_benchmarks_mutations_and_symmetry_controls_are_exact() -> None:
    report = _report()
    assert len(report["analytic_benchmarks"]) == 4
    assert all(row["status"] == "NOT_EXECUTED" for row in report["analytic_benchmarks"])
    assert len(report["deliberate_mutations"]) == 5
    assert all(row["expected_result"] == "DESIGNATED_CONTROL_FAILS" for row in report["deliberate_mutations"])
    assert len(report["symmetry_phase_controls"]) == 7


def test_convergence_contract_has_floor_ladders_and_fail_closed_tolerances() -> None:
    convergence = _report()["convergence_contract"]
    assert convergence["torque_floor_N_m"] == 1.0e-22
    assert convergence["angular_samples"] == [128, 256, 512]
    assert convergence["density_cubature_orders"] == [8, 12, 16, 24]
    assert convergence["energy_derivative_steps_rad"] == [1.0e-3, 5.0e-4, 2.5e-4, 1.25e-4]
    assert convergence["fail_closed"] is True


def test_sixteen_deterministic_maps_have_nominals_ranges_and_exact_effects() -> None:
    perturbations = _report()["deterministic_perturbations"]
    assert perturbations["count"] == 16
    assert len(perturbations["rows"]) == 16
    for row in perturbations["rows"]:
        assert "nominal" in row
        assert "test_range" in row
        assert "exact_map" in row
    assert perturbations["stochastic_priors"] == "NONE"


def test_jacobian_identifiability_rule_is_fail_closed() -> None:
    jacobian = _report()["jacobian_identifiability_contract"]
    assert jacobian["row_count"] == 150
    assert jacobian["column_count"] == 17
    assert jacobian["rank_relative_singular_value_threshold"] == 1.0e-10
    assert jacobian["identifiable_eta_threshold"] == 1.0e-3
    assert jacobian["indistinguishable_eta_threshold"] == 1.0e-6
    assert jacobian["minimum_contiguous_identifiable_lambda_points"] == 5
    assert jacobian["expected_exact_amplitude_degeneracy"] == [
        "TORQUE_CALIBRATION",
        "SOURCE_DENSITY_SCALE",
        "DETECTOR_DENSITY_SCALE",
    ]


def test_work_controls_outputs_and_review_outcomes_are_unexecuted() -> None:
    report = _report()
    assert len(report["work_packages"]) == 10
    assert all(row["status"] == "NOT_EXECUTED" for row in report["work_packages"])
    assert len(report["execution_controls"]) == 15
    assert all(row["status"] == "NOT_EXECUTED" for row in report["execution_controls"])
    assert len(report["canonical_output_classes"]) == 5
    assert all(row["status"] == "NOT_PRODUCED" for row in report["canonical_output_classes"])
    assert report["packet_review_outcomes"] == list(packet.PACKET_REVIEW_OUTCOMES)


def test_scope_authorizes_no_execution_stochastic_result_or_adoption() -> None:
    scope = _report()["scope"]
    allowed_true = {
        "packet_preparation_executed",
        "exact_harmonic_convention_frozen",
        "shared_production_kernel_frozen",
        "analytic_torque_and_cross_checks_frozen",
        "benchmark_mutation_and_symmetry_controls_frozen",
        "convergence_contract_frozen",
        "deterministic_perturbation_maps_frozen",
        "jacobian_identifiability_contract_frozen",
        "canonical_serialization_frozen",
    }
    for key, value in scope.items():
        assert value is (key in allowed_true), key


def test_thirty_preparation_controls_and_human_claim_boundary() -> None:
    report = _report()
    controls = report["preparation_controls"]
    assert controls["control_count"] == controls["pass_count"] == 30
    assert controls["failure_count"] == 0
    human = (REPO_ROOT / packet.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        "DETERMINISTIC FORWARD-MODEL VALIDATION CONTRACT",
        "Five-point central differentiation",
        "150 real",
        "Sixteen deterministic perturbation maps",
        "Gaussian noise:",
        packet.SELECTED_NEXT_TARGET,
    ):
        assert token in human

