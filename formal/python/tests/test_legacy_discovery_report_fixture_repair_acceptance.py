from __future__ import annotations

import hashlib
import json

from formal.python.tools import legacy_discovery_report_fixture_repair_acceptance as acceptance


EXPECTED_SHA256 = "b1b0a6a68653e8f7e8e88eaf771be8ae1999f65131f3886d753031504a14a5f8"


def _artifact() -> dict:
    return json.loads(acceptance.OUTPUT_PATH.read_text(encoding="utf-8"))


def test_acceptance_is_deterministic_from_detached_source_commit() -> None:
    raw = acceptance.canonical_json_bytes(acceptance.build_acceptance())
    assert acceptance.OUTPUT_PATH.read_bytes() == raw
    assert hashlib.sha256(raw).hexdigest() == EXPECTED_SHA256


def test_raw_clean_focused_acceptance_is_exact_and_teardown_is_clean() -> None:
    row = _artifact()["raw_detached_clean_checkout"]
    assert row["validation_result"] == "PASS"
    assert row["passed_test_count"] == 195
    assert row["combined_manifest_path_count"] == 59
    assert row["initial_runtime_path_absent_count"] == row["runtime_path_count"] == 21
    assert row["teardown_runtime_path_absent_count"] == 21
    assert row["detached_worktree_git_clean_before"] is True
    assert row["detached_worktree_git_clean_after"] is True


def test_aggregate_timeout_is_not_misreported_as_green_or_failed() -> None:
    artifact = _artifact()
    ceiling = artifact["validation_ceiling"]
    assert ceiling["full_python_aggregate_timed_out"] is True
    assert ceiling["full_python_aggregate_passed"] is False
    assert ceiling["full_python_aggregate_failed"] is False
    assert ceiling["full_python_aggregate_elapsed_timeout_seconds"] == 1800
    assert artifact["boundary"]["full_python_aggregate_claimed_green"] is False


def test_acceptance_preserves_authority_and_registry_nonexecution() -> None:
    artifact = _artifact()
    assert artifact["authorization"]["scientific_target"] == acceptance.SCIENTIFIC_TARGET
    assert artifact["authorization"]["maintenance_target"] == acceptance.MAINTENANCE_TARGET
    assert artifact["authorization"]["registry_migration_execution_authorized"] is False
    assert all(value is False for value in artifact["boundary"].values())


def test_acceptance_lean_certificate_binds_scoped_validation_ceiling() -> None:
    lean = (
        acceptance.REPO_ROOT
        / "formal/toe_formal/ToeFormal/Release/LegacyDiscoveryReportFixtureRepairAcceptance.lean"
    ).read_text(encoding="utf-8")
    assert EXPECTED_SHA256 in lean
    assert acceptance.EXPECTED_CORRECTION_SHA256 in lean
    assert acceptance.SCIENTIFIC_TARGET in lean
    assert "focusedRawCleanAcceptancePassed : Bool := true" in lean
    assert "fullPythonAggregatePassed : Bool := false" in lean
    assert "registryMigrationExecutionAuthorized : Bool := false" in lean
