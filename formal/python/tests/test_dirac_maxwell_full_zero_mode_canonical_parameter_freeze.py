from __future__ import annotations

import pytest

from formal.python.tools import dirac_maxwell_full_zero_mode_canonical_parameter_freeze as freeze


@pytest.fixture(scope="module")
def artifacts() -> tuple[dict, dict, dict, dict]:
    return freeze.build_artifacts()


def test_freeze_artifacts_are_current(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, matrix, manifest, report = artifacts
    assert freeze.PACKET_PATH.read_bytes() == freeze.canonical_json_bytes(packet)
    assert freeze.RUN_MATRIX_PATH.read_bytes() == freeze.canonical_json_bytes(matrix)
    assert freeze.MANIFEST_PATH.read_bytes() == freeze.canonical_json_bytes(manifest)
    assert freeze.REPORT_PATH.read_bytes() == freeze.canonical_json_bytes(report)


def test_exact_evidence_chain_and_historical_blocker_are_bound(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, _, _, _ = artifacts
    assert len(packet["input_artifacts"]) == len(freeze.INPUT_HASHES) == 12
    assert {item["path"]: item["sha256"] for item in packet["input_artifacts"]} == freeze.INPUT_HASHES
    assert packet["identity_policy"]["v0_blocker_preserved"] == "REGISTERED_RUN_IDENTITIES_NOT_UNIQUE"


def test_primary_parameters_and_complete_run_matrix_are_preregistered(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, matrix, _, _ = artifacts
    assert packet["proposed_canonical_parameters"] == {"N": 32, "dt": 0.0015625, "duration": 0.05, "max_iterations": 80, "solver_tolerance": 1e-12}
    assert packet["parameter_provenance"]["selection_is_cross_product_not_an_observed_single_pilot_tuple"] is True
    assert matrix["record_count"] == matrix["unique_run_id_count"] == 50
    assert matrix["role_counts"] == {
        "DETERMINISTIC_DUPLICATE": 2,
        "NEGATIVE_CONTROL": 27,
        "POSITIVE_CONTROL": 12,
        "PRIMARY_COUPLED": 1,
        "SOLVER_TOLERANCE_VERIFY": 2,
        "SPATIAL_REFINEMENT": 3,
        "TEMPORAL_REFINEMENT": 3,
    }
    assert all(record["output_path"].endswith(f"/{record['run_id']}.json") for record in matrix["records"])


def test_all_thresholds_are_mechanically_reconstructed(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, _, _, report = artifacts
    thresholds = packet["threshold_provenance"]
    assert len(thresholds) == report["threshold_count"] == 20
    assert all(item["candidate_canonical_value"] == item["recomputed_value"] for item in thresholds)
    assert all(item["generation_formula"] == "round_up_one_significant(2 * pilot_measured_value)" for item in thresholds)
    assert all(len(item["pilot_source_run_ids"]) == 13 for item in thresholds)


def test_exchange_signal_is_separated_from_drift_and_noise(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, _, _, _ = artifacts
    exchange = packet["exchange_signal_separation"]
    assert len(exchange["pilot_rows"]) == 2
    assert exchange["minimum_pilot_ratio"] > 300
    assert exchange["canonical_minimum_exchange_ratio"] == 100
    assert exchange["canonical_minimum_transverse_signal"] == 3e-8
    assert all(row["maximum_transverse_descendant_change"] > row["maximum_total_energy_drift"] for row in exchange["pilot_rows"])


def test_convergence_solver_energy_and_failure_semantics_are_frozen(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, _, _, _ = artifacts
    convergence = packet["convergence_definitions"]
    assert convergence["spatial"]["minimum_order"] == 0.8
    assert convergence["temporal_phi2"]["minimum_order"] == 1.5
    assert convergence["temporal_energy"]["minimum_order"] == 1.5
    assert convergence["Wilson_dispersion"]["grids"] == [64, 128, 256]
    assert convergence["outlier_policy"].startswith("no run may be excluded")
    assert convergence["post_execution_fit_range_changes"] == "forbidden"
    solver = packet["solver_freeze"]
    assert solver["tolerance"] == 1e-12
    assert solver["relative_tolerance"] is False
    assert solver["maximum_iterations"] == 80
    assert solver["initial_guess"].startswith("one explicit-Euler predictor")
    energy = packet["energy_freeze"]
    assert energy["classification"] == "BOUNDED_CONVERGENT_ENERGY_ERROR"
    assert len(energy["registered_components"]) == 8
    assert energy["Wilson_zero_mode_and_descendant_terms_required"] is True
    assert "forbidden" in packet["failure_semantics"]["threshold_relaxation_request"]


def test_preparation_authorizes_review_only(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, _, _, report = artifacts
    assert report["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
    assert packet["selected_next_target"] == freeze.REVIEW_TARGET
    assert packet["post_acceptance_target"] == freeze.POST_ACCEPTANCE_TARGET
    assert all(value is False for value in packet["boundary"].values())
    assert report["canonical_execution_authorized"] is False
    assert report["scientific_result_claimed"] is False


def test_prompt_is_preserved() -> None:
    assert freeze.PROMPT_DEPENDENCY_ROLE == "DEMOTE_TO_NONBLOCKING_PROVENANCE"
