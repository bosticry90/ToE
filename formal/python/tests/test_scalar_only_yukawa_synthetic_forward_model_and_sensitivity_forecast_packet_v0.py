from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    scalar_only_yukawa_synthetic_forward_model_and_sensitivity_forecast_packet_v0
    as packet,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / packet.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_packet_regenerates_and_consumes_exact_authority() -> None:
    assert packet.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == packet.TARGET
    assert report["verdict"] == packet.VERDICT
    assert report["selected_next_target"] == packet.SELECTED_NEXT_TARGET
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_scope_closure_artifacts"]
    } == packet.AUTHORITY_HASHES


def test_status_is_synthetic_only_and_unexecuted() -> None:
    status = _report()["scientific_status"]
    assert status == {
        "result_type": "SYNTHETIC_COMPUTATIONAL_FORECAST",
        "measured_evidence": "NONE",
        "eotwash_reproduction": "NO",
        "empirical_constraint": "NO",
        "scalar_branch_adoption": "NO",
        "simulation_execution": "NOT_AUTHORIZED",
    }


def test_two_model_levels_and_geometry_are_exact() -> None:
    report = _report()
    levels = report["forward_model_levels"]
    assert len(levels) == 2
    assert levels[0]["level"] == "ANALYTIC_BENCHMARK"
    assert len(levels[0]["benchmarks"]) == 4
    assert levels[1]["level"] == "IDEALIZED_TORSION_BALANCE"
    geometry = report["idealized_geometry"]
    assert geometry["detector_sphere_count"] == 2
    assert geometry["attractor_sphere_count"] == 2
    assert geometry["sphere_density_kg_m3"] == 19250.0
    assert geometry["gap_count"] == 25
    assert geometry["not_eotwash_reconstruction"] is True


def test_grid_harmonics_and_observation_count_are_exact() -> None:
    report = _report()
    grid = report["lambda_grid"]
    assert grid["positive_grid_count"] == 25
    assert grid["minimum_m"] == 1.0e-5
    assert grid["maximum_m"] == 1.0e-1
    harmonic = report["harmonic_contract"]
    assert harmonic["retained_harmonics"] == [2, 4, 6]
    assert harmonic["quadratures_per_harmonic"] == 2
    assert harmonic["observation_count"] == 150


def test_noise_covariance_and_nuisance_contract_are_frozen() -> None:
    report = _report()
    noise = report["synthetic_observation_model"]["noise"]
    assert noise["distribution"] == "ZERO_MEAN_MULTIVARIATE_GAUSSIAN"
    assert len(noise["channel_sigma_N_m"]) == 6
    assert noise["gap_log_correlation_length"] == 0.55
    nuisances = report["nuisance_contract"]
    assert nuisances["nuisance_count"] == 11
    assert len(nuisances["rows"]) == 11
    assert any(row["nuisance_id"] == "GAP_OFFSET" for row in nuisances["rows"])
    assert any(row["nuisance_id"] == "HARMONIC_LEAKAGE" for row in nuisances["rows"])


def test_trial_and_boundary_calibration_are_exact() -> None:
    report = _report()
    trials = report["trial_contract"]
    assert trials["base_seed"] == 2026071801
    assert trials["null_trial_count"] == 2000
    assert trials["injection_trials_per_positive_lambda"] == 1000
    inference = report["recovery_and_boundary_contract"]
    assert inference["wilks_threshold_authorized"] is False
    assert inference["null_critical_value"] == "EMPIRICAL_95TH_PERCENTILE"
    assert inference["pointwise_coverage_calibrated"] is True


def test_degeneracy_controls_outputs_and_work_packages_are_unexecuted() -> None:
    report = _report()
    assert len(report["degeneracy_variants"]) == 7
    assert len(report["shared_controls"]) == 11
    assert all(row["status"] == "NOT_EXECUTED" for row in report["shared_controls"])
    assert len(report["required_output_classes"]) == 8
    assert all(row["status"] == "NOT_PRODUCED" for row in report["required_output_classes"])
    assert len(report["work_packages"]) == 8
    assert all(row["status"] == "NOT_EXECUTED" for row in report["work_packages"])


def test_review_outcomes_and_preparation_controls_are_complete() -> None:
    report = _report()
    assert report["packet_review_outcomes"] == list(packet.PACKET_REVIEW_OUTCOMES)
    controls = report["preparation_controls"]
    assert controls["control_count"] == controls["pass_count"] == 24
    assert controls["failure_count"] == 0
    assert all(row["status"] == "PASS" for row in controls["rows"])


def test_scope_authorizes_no_execution_empirical_claim_or_adoption() -> None:
    scope = _report()["scope"]
    allowed_true = {
        "packet_preparation_executed",
        "comparison_only_provenance_frozen",
        "fixed_yukawa_amplitude_one_third",
        "two_forward_model_levels_frozen",
        "extended_source_transport_frozen",
        "synthetic_noise_nuisance_contract_frozen",
        "boundary_coverage_contract_frozen",
        "standing_no_contact_policy_retained",
    }
    for key, value in scope.items():
        assert value is (key in allowed_true), key


def test_human_packet_records_exact_claim_firewall_and_next_target() -> None:
    text = (REPO_ROOT / packet.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        "SYNTHETIC COMPUTATIONAL FORECAST",
        "Eöt-Wash reproduction:",
        "NOT AUTHORIZED",
        "19250 kg m^-3",
        "2000",
        "1000",
        "Wilks",
        packet.SELECTED_NEXT_TARGET,
    ):
        assert token in text
