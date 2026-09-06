from __future__ import annotations

import pytest

from formal.python.tools import dirac_maxwell_full_zero_mode_non_authoritative_pilot_v1 as pilot


@pytest.fixture(scope="module")
def artifacts() -> tuple[dict, dict, dict, dict]:
    return pilot.build_artifacts()


def test_pilot_v1_artifacts_are_current(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, arrays, manifest, report = artifacts
    assert pilot.PACKET_PATH.read_bytes() == pilot.canonical_json_bytes(packet)
    assert pilot.ARRAYS_PATH.read_bytes() == pilot.canonical_json_bytes(arrays)
    assert pilot.MANIFEST_PATH.read_bytes() == pilot.canonical_json_bytes(manifest)
    assert pilot.REPORT_PATH.read_bytes() == pilot.canonical_json_bytes(report)


def test_pilot_v1_is_engineering_ready_but_non_authoritative(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, _, _, report = artifacts
    assert packet["outcome"] == "ENGINEERING_READY"
    assert all(packet["summary"]["criteria"].values())
    assert report["verdict"] == "ENGINEERING_READY_PENDING_INDEPENDENT_REVIEW"
    assert packet["selected_next_target"] == pilot.REVIEW_TARGET
    assert packet["canonical_parameters_frozen"] is False
    assert packet["canonical_thresholds_frozen"] is False
    assert packet["canonical_execution_authorized"] is False
    assert packet["scientific_result_claimed"] is False


def test_all_run_records_have_unique_role_qualified_identity(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, arrays, _, _ = artifacts
    records = arrays["runs"]
    assert len(records) == 13
    assert len({record["run_record_id"] for record in records}) == 13
    assert len({record["calibration_role"] for record in records}) == 13
    assert all(record["run_id"] == record["run_record_id"] == f"{record['calibration_role']}:{record['execution_id']}" for record in records)
    identity = packet["summary"]["identity_repair"]
    assert identity["run_record_count"] == identity["unique_run_record_count"] == 13
    assert len(identity["shared_execution_ids"]) == 2


def test_numerical_series_are_byte_for_byte_equal_to_v0(artifacts: tuple[dict, dict, dict, dict]) -> None:
    _, arrays, _, _ = artifacts
    v0_arrays = pilot.load_json(pilot.REPO_ROOT / pilot.pilot_v0.ARRAYS_RELATIVE_PATH)
    assert len(arrays["runs"]) == len(v0_arrays["runs"])
    for repaired, original in zip(arrays["runs"], v0_arrays["runs"], strict=True):
        assert repaired["legacy_run_id"] == original["run_id"]
        assert repaired["series"] == original["series"]


def test_controls_residuals_and_threshold_candidates_are_unchanged(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, _, _, _ = artifacts
    v0_packet = pilot.load_json(pilot.REPO_ROOT / pilot.pilot_v0.PACKET_RELATIVE_PATH)
    summary = packet["summary"]
    v0_summary = v0_packet["summary"]
    assert summary["maximum_residuals"] == v0_summary["maximum_residuals"]
    assert summary["candidate_thresholds_unreviewed"] == v0_summary["candidate_thresholds_unreviewed"]
    assert summary["positive_controls"] == v0_summary["positive_controls"]
    assert summary["negative_controls"] == v0_summary["negative_controls"]


def test_two_clean_v1_processes_are_byte_identical(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, _, _, _ = artifacts
    determinism = packet["determinism"]
    assert determinism["execution_count"] == 2
    assert determinism["byte_identical"] is True
    assert len(set(determinism["execution_sha256"])) == 1


def test_prompt_is_preserved() -> None:
    assert pilot.PROMPT_DEPENDENCY_ROLE == "DEMOTE_TO_NONBLOCKING_PROVENANCE"
