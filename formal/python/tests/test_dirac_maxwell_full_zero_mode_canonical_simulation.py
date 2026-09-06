from __future__ import annotations

import pytest

from formal.python.tools import dirac_maxwell_full_zero_mode_canonical_simulation as execution


@pytest.fixture(scope="module")
def artifacts() -> tuple[dict, dict, dict, dict, list]:
    return execution.build_execution()


def test_canonical_execution_artifacts_are_current(artifacts: tuple[dict, dict, dict, dict, list]) -> None:
    packet, arrays, manifest, report, run_payloads = artifacts
    assert execution.PACKET_PATH.read_bytes() == execution.canonical_json_bytes(packet)
    assert execution.ARRAYS_PATH.read_bytes() == execution.canonical_json_bytes(arrays)
    assert execution.MANIFEST_PATH.read_bytes() == execution.canonical_json_bytes(manifest)
    assert execution.REPORT_PATH.read_bytes() == execution.canonical_json_bytes(report)
    assert all(path.read_bytes() == execution.canonical_json_bytes(payload) for path, payload in run_payloads)


def test_all_fifty_frozen_records_are_preserved_with_hashes(artifacts: tuple[dict, dict, dict, dict, list]) -> None:
    packet, _, manifest, _, run_payloads = artifacts
    assert packet["run_count"] == len(packet["run_index"]) == len(run_payloads) == 50
    assert len({item["run_id"] for item in packet["run_index"]}) == 50
    assert all(item["completion_status"] == "COMPLETED" for item in packet["run_index"])
    assert len(manifest["run_outputs"]) == 50
    assert all(item["output_sha256"] == execution.sha256_path(execution.REPO_ROOT / item["output_path"]) for item in packet["run_index"])


def test_every_run_preserves_required_execution_evidence(artifacts: tuple[dict, dict, dict, dict, list]) -> None:
    _, _, _, _, run_payloads = artifacts
    for _, payload in run_payloads:
        assert payload["run_id"]
        assert payload["run_role"]
        assert payload["input_hash"]
        assert payload["environment_identity_hash"]
        assert payload["completion_status"] == "COMPLETED"
        assert payload["expected_control_outcome"]
        assert payload["actual_control_outcome"]
        assert payload["numeric_payload_hash"]
        assert payload["scientific_interpretation"] == "PENDING_INDEPENDENT_RESULT_REVIEW"


def test_controls_thresholds_and_determinism_match_mechanically(artifacts: tuple[dict, dict, dict, dict, list]) -> None:
    packet, _, _, _, _ = artifacts
    observed = packet["mechanical_observations_not_a_scientific_verdict"]
    assert observed["positive_control_match_count"] == 12
    assert observed["negative_control_match_count"] == 27
    assert observed["all_simulation_threshold_evaluations_passed"] is True
    assert observed["deterministic_duplicates_match"] is True
    assert len(set(observed["deterministic_numeric_payload_hashes"])) == 1


def test_frozen_convergence_and_exchange_observations_are_recorded(artifacts: tuple[dict, dict, dict, dict, list]) -> None:
    packet, _, _, _, _ = artifacts
    observed = packet["mechanical_observations_not_a_scientific_verdict"]
    assert observed["spatial_phi2_order"] >= 0.8
    assert observed["temporal_phi2_order"] >= 1.5
    assert observed["temporal_energy_order"] >= 1.5
    assert observed["Wilson_dispersion"]["observed_continuum_order"] >= 0.8
    exchange = observed["primary_exchange"]
    assert exchange["exchange_ratio"] >= 100
    assert exchange["maximum_transverse_descendant_change"] >= 3e-8
    assert observed["primary_energy_drift_class"] == "OSCILLATORY_OR_BOUNDED"


def test_execution_does_not_assign_its_own_scientific_verdict(artifacts: tuple[dict, dict, dict, dict, list]) -> None:
    packet, _, _, report, _ = artifacts
    assert packet["execution_status"] == "COMPLETE_PENDING_INDEPENDENT_RESULT_REVIEW"
    assert packet["first_completed_canonical_matrix_preserved"] is True
    assert packet["interpretation_driven_rerun_performed"] is False
    assert packet["selected_next_target"] == execution.REVIEW_TARGET
    assert packet["canonical_result_accepted"] is False
    assert packet["scientific_result_claimed"] is False
    assert report["canonical_result_accepted"] is False
    assert report["scientific_result_claimed"] is False


def test_prompt_is_preserved() -> None:
    assert execution.PROMPT_DEPENDENCY_ROLE == "DEMOTE_TO_NONBLOCKING_PROVENANCE"
