from __future__ import annotations

import hashlib
import json

from formal.python.tools import legacy_discovery_report_fixture_repair as repair


EXPECTED_SHA256 = "e70d8741de6378e4f00bb135607cb92b06ad83ee8b78e0675b93a6226720f9eb"


def _artifact() -> dict:
    return json.loads(repair.OUTPUT_PATH.read_text(encoding="utf-8"))


def test_repair_artifact_is_deterministic_and_current() -> None:
    raw = repair.canonical_json_bytes(repair.build_artifact())
    assert repair.OUTPUT_PATH.read_bytes() == raw
    assert hashlib.sha256(raw).hexdigest() == EXPECTED_SHA256


def test_repair_installs_only_three_exact_historical_roots() -> None:
    rows = _artifact()["root_fixtures"]
    assert len(rows) == 3
    assert sum(row["size_bytes"] for row in rows) == 17_567
    for row in rows:
        raw = (repair.REPO_ROOT / row["path"]).read_bytes()
        assert len(raw) == row["size_bytes"]
        assert hashlib.sha256(raw).hexdigest() == row["sha256"]


def test_repair_contract_is_bounded_and_raw_clean_acceptance_remains_pending() -> None:
    artifact = _artifact()
    implementation = artifact["implementation"]
    assert implementation["affected_test_count"] == 20
    assert implementation["root_fixture_count"] == 3
    assert implementation["derived_report_count"] == 18
    assert implementation["report_node_count"] == 21
    assert implementation["derived_dependency_edge_count"] == 35
    assert artifact["validation"] == {
        "affected_and_materializer_focused_pass_count": 27,
        "focused_validation_passed": True,
        "raw_detached_clean_checkout_full_manifest_passed": False,
        "raw_detached_clean_checkout_validation_pending": True,
    }
    assert all(value is False for value in artifact["boundary"].values())


def test_repair_preserves_authority_and_registry_nonexecution() -> None:
    authorization = _artifact()["authorization"]
    assert authorization["scientific_target"] == repair.SCIENTIFIC_TARGET
    assert authorization["maintenance_target"] == repair.MAINTENANCE_TARGET
    assert authorization["registry_migration_execution_authorized"] is False


def test_repair_lean_certificate_binds_pending_acceptance_boundary() -> None:
    lean = (
        repair.REPO_ROOT
        / "formal/toe_formal/ToeFormal/Release/LegacyDiscoveryReportFixtureRepair.lean"
    ).read_text(encoding="utf-8")
    assert EXPECTED_SHA256 in lean
    assert repair.SCIENTIFIC_TARGET in lean
    assert repair.MAINTENANCE_TARGET in lean
    assert "rawDetachedCleanCheckoutAccepted : Bool := false" in lean
    assert "registryMigrationExecutionAuthorized : Bool := false" in lean
