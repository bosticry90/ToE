from __future__ import annotations

import hashlib
import json
import subprocess

from formal.python.tools import (
    legacy_discovery_report_fixture_repair_correction_v1 as correction,
)


EXPECTED_SHA256 = "7befc5fd9500d2e099a26013eed159a6ece9dff1a3c29365a6c53314cd19b940"


def _artifact() -> dict:
    return json.loads(correction.OUTPUT_PATH.read_text(encoding="utf-8"))


def test_v1_correction_is_deterministic_from_committed_git_bytes() -> None:
    raw = correction.canonical_json_bytes(correction.build_correction())
    assert correction.OUTPUT_PATH.read_bytes() == raw
    assert hashlib.sha256(raw).hexdigest() == EXPECTED_SHA256


def test_v1_corrects_only_checkout_sensitive_source_identity() -> None:
    artifact = _artifact()
    row = artifact["correction"]
    assert row["corrected_path"] == "formal/python/tests/conftest.py"
    assert row["reason"] == (
        "V0_BOUND_MIXED_EOL_WORKTREE_BYTES_INSTEAD_OF_COMMITTED_GIT_BYTES"
    )
    assert row["old_worktree_sha256"] != row["new_committed_sha256"]
    assert artifact["supersedes_v0_sha256"] == correction.EXPECTED_V0_SHA256
    assert all(value is False for value in artifact["boundary"].values())


def test_every_corrected_implementation_identity_matches_source_commit() -> None:
    for row in _artifact()["implementation_files"]:
        raw = subprocess.run(
            ["git", "show", f"{correction.SOURCE_COMMIT}:{row['path']}"],
            cwd=correction.REPO_ROOT,
            capture_output=True,
            check=True,
        ).stdout
        assert len(raw) == row["size_bytes"]
        assert hashlib.sha256(raw).hexdigest() == row["sha256"]
        assert row["hash_policy"] == "EXACT_COMMITTED_GIT_BLOB_BYTES"


def test_v1_preserves_repair_scope_authority_and_pending_acceptance() -> None:
    artifact = _artifact()
    assert artifact["implementation"]["affected_test_count"] == 20
    assert artifact["implementation"]["report_node_count"] == 21
    assert artifact["authorization"]["scientific_target"] == correction.SCIENTIFIC_TARGET
    assert artifact["authorization"]["maintenance_target"] == correction.MAINTENANCE_TARGET
    assert artifact["authorization"]["registry_migration_execution_authorized"] is False
    assert artifact["validation"]["fixture_chain_failure_count"] == 0
    assert artifact["validation"]["raw_detached_clean_checkout_validation_pending"] is True


def test_v1_lean_certificate_binds_correction_and_nonpromotion() -> None:
    lean = (
        correction.REPO_ROOT
        / "formal/toe_formal/ToeFormal/Release/LegacyDiscoveryReportFixtureRepairCorrectionV1.lean"
    ).read_text(encoding="utf-8")
    assert EXPECTED_SHA256 in lean
    assert correction.EXPECTED_V0_SHA256 in lean
    assert correction.SCIENTIFIC_TARGET in lean
    assert "rawDetachedCleanCheckoutAccepted : Bool := false" in lean
    assert "registryMigrationExecutionAuthorized : Bool := false" in lean
