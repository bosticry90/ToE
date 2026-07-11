from __future__ import annotations

import hashlib
import json
import subprocess

from formal.python.tools import legacy_discovery_report_fixture_packet as packet


EXPECTED_SHA256 = "09abc2032a3219369d376c7f573a2c65a2618ec8af7105b1e227950b84febeb6"


def _artifact() -> dict:
    return json.loads(packet.OUTPUT_PATH.read_text(encoding="utf-8"))


def test_packet_is_deterministic_and_current() -> None:
    expected = packet.canonical_json_bytes(packet.build_packet())
    assert packet.OUTPUT_PATH.read_bytes() == expected
    assert hashlib.sha256(expected).hexdigest() == EXPECTED_SHA256


def test_packet_freezes_exact_clean_checkout_failure_and_fixture_scope() -> None:
    artifact = _artifact()
    inventory = artifact["clean_checkout_failure_inventory"]
    assert inventory == {
        "affected_test_count": 20,
        "affected_tests": packet.FAILING_TESTS,
        "derived_report_count": 18,
        "raw_manifest_failure_count_before_repair": 20,
        "raw_manifest_pass_count_before_repair": 147,
        "root_fixture_count": 3,
    }
    contract = artifact["fixture_contract"]
    assert len(contract["root_fixtures"]) == 3
    assert len(contract["derived_reports"]) == 18
    assert len({row["output_path"] for row in contract["derived_reports"]}) == 18
    assert [row["chain_index"] for row in contract["derived_reports"]] == list(
        range(1, 19)
    )


def test_packet_binds_compact_root_fixture_hashes_absent_at_preparation_commit() -> None:
    roots = _artifact()["fixture_contract"]["root_fixtures"]
    assert sum(row["size_bytes"] for row in roots) == 17_567
    assert {row["sha256"] for row in roots} == {
        "802d1e8409bd1cc5602dc11db619bdbd757d4c9a0759709247ae2a6d366442c5",
        "73489f4c96f221d214703e227a4887bda5274490fc6dbcb31da2b44c9e7f0822",
        "07af32ad04bbcea569a8256a12462404a0ca3334f51dca23eae3e0830ba81a94",
    }
    for row in roots:
        historical_lookup = subprocess.run(
            [
                "git",
                "cat-file",
                "-e",
                f"{packet.SOURCE_COMMIT}:{row['planned_fixture_path']}",
            ],
            cwd=packet.REPO_ROOT,
            capture_output=True,
            check=False,
        )
        assert historical_lookup.returncode != 0


def test_packet_source_inventory_is_bound_to_preparation_commit() -> None:
    artifact = _artifact()
    inventory = artifact["source_inventory"]
    assert len(inventory["test_files"]) == 20
    assert len(inventory["producer_files"]) == 18
    for row in inventory["test_files"] + inventory["producer_files"]:
        raw = subprocess.run(
            ["git", "show", f"{packet.SOURCE_COMMIT}:{row['path']}"],
            cwd=packet.REPO_ROOT,
            capture_output=True,
            check=True,
        ).stdout
        assert hashlib.sha256(raw).hexdigest() == row["sha256"]
        assert len(raw) == row["size_bytes"]


def test_packet_preserves_authority_and_authorizes_no_fixture_execution() -> None:
    artifact = _artifact()
    authorization = artifact["authorization"]
    assert authorization["scientific_target"] == packet.SCIENTIFIC_TARGET
    assert authorization["maintenance_target"] == packet.MAINTENANCE_TARGET
    assert authorization["next_action"] == packet.REVIEW_TARGET
    assert authorization["fixture_repair_execution_authorized"] is False
    assert authorization["registry_migration_execution_authorized"] is False
    assert all(value is False for value in artifact["boundary"].values())


def test_packet_freezes_negative_controls_and_lean_certificate() -> None:
    artifact = _artifact()
    assert artifact["negative_control_count"] == len(packet.NEGATIVE_CONTROLS) == 12
    assert artifact["negative_controls"] == packet.NEGATIVE_CONTROLS
    lean = (
        packet.REPO_ROOT
        / "formal/toe_formal/ToeFormal/Release/LegacyDiscoveryReportFixturePacket.lean"
    ).read_text(encoding="utf-8")
    assert EXPECTED_SHA256 in lean
    assert packet.SCIENTIFIC_TARGET in lean
    assert packet.MAINTENANCE_TARGET in lean
    assert "fixtureRepairExecutionAuthorized : Bool := false" in lean
    assert "registryMigrationExecutionAuthorized : Bool := false" in lean
