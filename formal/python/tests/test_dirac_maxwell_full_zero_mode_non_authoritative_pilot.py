from __future__ import annotations

import pytest

from formal.python.tools import dirac_maxwell_full_zero_mode_non_authoritative_pilot as pilot


@pytest.fixture(scope="module")
def artifacts() -> tuple[dict, dict, dict, dict]:
    return pilot.build_artifacts()


def test_pilot_artifacts_are_current(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, arrays, manifest, report = artifacts
    assert pilot.PACKET_PATH.read_bytes() == pilot.canonical_json_bytes(packet)
    assert pilot.ARRAYS_PATH.read_bytes() == pilot.canonical_json_bytes(arrays)
    assert pilot.MANIFEST_PATH.read_bytes() == pilot.canonical_json_bytes(manifest)
    assert pilot.REPORT_PATH.read_bytes() == pilot.canonical_json_bytes(report)


def test_outcome_is_engineering_ready_but_non_authoritative(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, _, _, report = artifacts
    assert packet["outcome"] == "ENGINEERING_READY"
    assert all(packet["summary"]["criteria"].values())
    assert packet["selected_next_target"] == pilot.REVIEW_TARGET
    assert packet["canonical_parameters_frozen"] is False
    assert packet["canonical_thresholds_frozen"] is False
    assert packet["canonical_execution_authorized"] is False
    assert packet["scientific_result_claimed"] is False
    assert report["verdict"] == "ENGINEERING_READY_PENDING_INDEPENDENT_REVIEW"


def test_common_charge_and_link_normalization_is_explicit(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, _, _, _ = artifacts
    normalization = packet["lattice_normalization"]
    assert normalization["positive_link"] == "U_n=exp(i q theta_n)"
    assert normalization["negative_link"] == "U_n*=exp(-i q theta_n)"
    assert normalization["source_charge_density"].startswith("J0_n=q")
    assert normalization["Gauss_law"] == "p_(n-1)-p_n+a J0_n=0"


def test_all_controls_discriminate_for_the_intended_reason(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, _, _, _ = artifacts
    summary = packet["summary"]
    positives = summary["positive_controls"]
    negatives = summary["negative_controls"]
    assert len(positives) == 12 and all(item["passed"] for item in positives)
    assert len(negatives) == 27 and all(item["passed"] for item in negatives)
    assert all(item["actual_diagnostics"] == [item["expected_diagnostic"]] for item in negatives)
    assert len({item["expected_diagnostic"] for item in negatives}) == 27


def test_link_dispersion_constraints_and_descendants_are_exercised(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, _, _, _ = artifacts
    summary = packet["summary"]
    dispersion = summary["dispersion"]
    controls = {item["control_id"]: item for item in summary["positive_controls"]}
    assert summary["maximum_residuals"]["link_norm"] <= 5e-15
    assert dispersion["maximum_discrete_formula_error"] < 1e-12
    assert dispersion["observed_continuum_order"] > 0.8
    assert dispersion["doubler_energy_monotonically_separated"] is True
    assert controls["J2_sources_phi2"]["passed"] is True
    assert controls["J3_sources_phi3"]["passed"] is True


def test_refinement_solver_and_energy_hierarchy_are_resolved(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, _, _, _ = artifacts
    summary = packet["summary"]
    temporal = summary["temporal_refinement"]
    hierarchy = summary["solver_hierarchy"]
    assert temporal["observed_phi2_order"] > 1.5
    assert temporal["observed_energy_error_order"] > 1.5
    assert hierarchy["observed_ratio"] <= hierarchy["required_ratio"] == 0.01
    assert summary["criteria"]["energy_error_bounded_and_refines"] is True


def test_registered_arrays_cover_equations_spectra_exchange_and_energy(artifacts: tuple[dict, dict, dict, dict]) -> None:
    _, arrays, _, _ = artifacts
    required = {
        "longitudinal_Maxwell_residual",
        "phi2_wave_residual",
        "phi3_wave_residual",
        "Dirac_plus_sector1_residual",
        "Dirac_plus_sector2_residual",
        "Dirac_minus_sector1_residual",
        "Dirac_minus_sector2_residual",
        "adjoint_plus_sector1_residual",
        "adjoint_plus_sector2_residual",
        "adjoint_minus_sector1_residual",
        "adjoint_minus_sector2_residual",
        "gauss_residual",
        "continuity_residual",
        "exchange_longitudinal",
        "exchange_phi2",
        "exchange_phi3",
        "exchange_combined",
        "psi_plus_positive_frequency_weight",
        "psi_plus_negative_frequency_weight",
        "psi_minus_positive_frequency_weight",
        "psi_minus_negative_frequency_weight",
        "periodic_boundary_flux",
        "total_energy_delta",
    }
    assert arrays["runs"]
    for run in arrays["runs"]:
        assert required <= set(run["series"])
        lengths = {len(values) for values in run["series"].values()}
        assert len(lengths) == 1


def test_threshold_candidates_follow_frozen_rule_but_are_not_frozen(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, _, _, _ = artifacts
    summary = packet["summary"]
    expected = {key: pilot.round_up_one_significant(2 * value) for key, value in summary["maximum_residuals"].items()}
    assert summary["candidate_thresholds_unreviewed"] == expected
    assert packet["canonical_thresholds_frozen"] is False


def test_two_clean_processes_are_byte_identical(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, _, _, _ = artifacts
    determinism = packet["determinism"]
    assert determinism["execution_count"] == 2
    assert determinism["byte_identical"] is True
    assert len(set(determinism["execution_sha256"])) == 1


def test_prompt_is_preserved() -> None:
    assert pilot.sha256_path(pilot.REPO_ROOT / pilot.PROMPT_RELATIVE_PATH) == pilot.PROMPT_SHA256
