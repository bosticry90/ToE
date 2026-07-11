from __future__ import annotations

import hashlib
import json

from formal.python.tools import (
    legacy_discovery_report_fixture_packet_independent_review as review,
)


EXPECTED_SHA256 = "cc38957def8b67d033f89b74496f95ef759cc0a871405673b899102bfbdcf6b0"


def _artifact() -> dict:
    return json.loads(review.OUTPUT_PATH.read_text(encoding="utf-8"))


def test_independent_review_is_deterministic_and_current() -> None:
    raw = review.canonical_json_bytes(review.build_review())
    assert review.OUTPUT_PATH.read_bytes() == raw
    assert hashlib.sha256(raw).hexdigest() == EXPECTED_SHA256


def test_review_accepts_only_the_bounded_fixture_repair() -> None:
    artifact = _artifact()
    assert artifact["status"] == (
        "ACCEPTED_PREPARATION_PACKET_AND_AUTHORIZED_BOUNDED_FIXTURE_REPAIR_ONLY"
    )
    authorization = artifact["authorization"]
    assert authorization["bounded_fixture_repair_execution_authorized"] is True
    assert authorization["registry_migration_execution_authorized"] is False
    assert authorization["scientific_target_rotation_authorized"] is False
    assert authorization["maintenance_target_rotation_authorized"] is False
    assert authorization["scientific_target"] == review.SCIENTIFIC_TARGET
    assert authorization["maintenance_target"] == review.MAINTENANCE_TARGET


def test_review_independently_binds_roots_and_dependency_graph() -> None:
    artifact = _artifact()
    roots = artifact["reviewed_root_fixtures"]
    assert len(roots) == 3
    assert sum(row["observed_size_bytes"] for row in roots) == 17_567
    assert all(
        row["verification"] == "INDEPENDENT_LOCAL_BYTE_OBSERVATION_MATCHED_PACKET"
        for row in roots
    )
    assert {
        (row["observed_size_bytes"], row["observed_sha256"]) for row in roots
    } == set(review.ROOT_OBSERVATIONS.values())
    graph = artifact["dependency_graph_review"]
    assert graph == {
        "declared_order_is_topological": True,
        "derived_dependency_edge_count": 35,
        "derived_node_count": 18,
        "root_lineage_edge_count": 3,
        "root_node_count": 3,
        "total_dependency_edge_count": 38,
        "total_node_count": 21,
    }


def test_review_preserves_nonpromotion_and_requires_clean_checkout_execution() -> None:
    artifact = _artifact()
    assert all(value is False for value in artifact["boundary"].values())
    assert artifact["negative_control_review"]["accepted_control_count"] == 12
    assert artifact["clean_checkout_evidence"]["prior_raw_manifest_failure_count"] == 20
    assert artifact["clean_checkout_evidence"]["prior_raw_manifest_pass_count"] == 147


def test_review_lean_certificate_binds_artifact_and_authority() -> None:
    lean = (
        review.REPO_ROOT
        / "formal/toe_formal/ToeFormal/Release/LegacyDiscoveryReportFixturePacketIndependentReview.lean"
    ).read_text(encoding="utf-8")
    assert EXPECTED_SHA256 in lean
    assert review.SCIENTIFIC_TARGET in lean
    assert review.MAINTENANCE_TARGET in lean
    assert "boundedFixtureRepairExecutionAuthorized : Bool := true" in lean
    assert "registryMigrationExecutionAuthorized : Bool := false" in lean
