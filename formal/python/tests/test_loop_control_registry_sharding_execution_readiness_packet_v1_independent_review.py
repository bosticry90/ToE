from __future__ import annotations

import hashlib
import json

from formal.python.tools import (
    loop_control_registry_sharding_execution_readiness_packet_v1_independent_review
    as review,
)


EXPECTED_REVIEW_SHA256 = (
    "54621eb5c109215ce7737e25cce37d8182256a6832fe186283df49d6b8125d4f"
)


def _artifact() -> dict:
    return json.loads(review.OUTPUT_PATH.read_text(encoding="utf-8"))


def test_v1_review_is_deterministic_from_immutable_corrective_commit() -> None:
    raw = review.canonical_json_bytes(review.build_review())
    assert review.OUTPUT_PATH.read_bytes() == raw
    assert hashlib.sha256(raw).hexdigest() == EXPECTED_REVIEW_SHA256


def test_v1_review_rejects_preparation_acceptance_and_all_execution() -> None:
    artifact = _artifact()
    assert artifact["status"] == (
        "REJECTED_CORRECTIVE_V1_PREPARATION_CONTRACT_INTERFACE_PATH_IDENTITY_"
        "CONTROL_AND_REPORT_DEFECTS_NO_EXECUTION_OR_AUTHORITY"
    )
    assert artifact["decision"].startswith("REJECT_CORRECTIVE_V1_PREPARATION")
    authorization = artifact["authorization"]
    assert authorization["corrective_v1_preparation_accepted"] is False
    assert authorization["prototype_selection_authorized"] is False
    assert authorization["migration_execution_authorized"] is False
    assert authorization["cutover_authorized"] is False
    assert authorization["scientific_target_rotation_authorized"] is False
    assert authorization["maintenance_target_rotation_authorized"] is False


def test_v1_review_reproduces_and_accepts_only_the_bounded_v0_corrections() -> None:
    accepted = _artifact()["accepted_corrections"]
    assert all(accepted.values())
    assert accepted["all_ten_schemas_pass_draft_2020_12_metaschema"] is True
    assert accepted["profile_closures_exact_ordered_and_nonambiguous"] is True
    assert accepted["base64_false_accept_rejected_structurally"] is True
    assert accepted["path_absolute_and_slash_unc_false_accepts_rejected_structurally"] is True
    assert accepted["original_52_migration_controls_byte_semantically_unchanged"] is True
    assert accepted["requirements_direct_and_transitive_validator_closure_pinned"] is True


def test_v1_review_records_all_six_fail_closed_findings() -> None:
    findings = _artifact()["findings"]
    assert [row["finding_id"] for row in findings] == [
        f"REGISTRY-READINESS-V1-REVIEW-{index:03d}" for index in range(1, 7)
    ]
    assert sum(row["severity"] == "HIGH" for row in findings) == 5
    assert sum(row["severity"] == "MEDIUM" for row in findings) == 1
    assert all(row["packet_defect"] is True for row in findings)
    assert all(row["status"].startswith("OPEN_") for row in findings)


def test_v1_review_proves_consumer_and_error_interface_path_failures() -> None:
    findings = {row["finding_id"]: row for row in _artifact()["findings"]}
    consumer = findings["REGISTRY-READINESS-V1-REVIEW-001"]
    assert consumer["incompatible_consumer_count"] == 3
    assert consumer["incompatible_consumer_paths"] == [
        ".gitattributes",
        ".vscode/settings.json",
        "Physics Imps and Sigs.txt",
    ]
    interface = findings["REGISTRY-READINESS-V1-REVIEW-002"]
    assert interface["interface_false_accept_paths"] == [
        "/tmp/registry.json",
        "//server/share/registry.json",
    ]
    assert interface["interface_rejected_readiness_control_ids"] == [
        f"REGISTRY-READINESS-V1-RC-{index:03d}" for index in range(1, 9)
    ]


def test_v1_review_proves_readiness_controls_are_not_executable_contracts() -> None:
    finding = _artifact()["findings"][2]
    assert finding["disjunctive_regression_ids"] == [
        "REGISTRY-READINESS-V1-RC-002",
        "REGISTRY-READINESS-V1-RC-003",
        "REGISTRY-READINESS-V1-RC-004",
        "REGISTRY-READINESS-V1-RC-008",
    ]
    gaps = finding["missing_execution_metadata_by_control"]
    assert set(gaps) == {
        f"REGISTRY-READINESS-V1-RC-{index:03d}" for index in range(1, 9)
    }
    required = {
        "artifact_kind",
        "fixture_isolation",
        "mutation_precondition",
        "mutator_entrypoint",
        "validator_profile",
    }
    assert all(required.issubset(set(missing)) for missing in gaps.values())


def test_v1_review_binds_record_custody_and_current_targets_without_promotion() -> None:
    artifact = _artifact()
    roots = artifact["custody_and_authority_review"]["record_commitments"]
    assert roots == {
        "authority_commitment_sha256": review.AUTHORITY_COMMITMENT_SHA256,
        "full_record_identity_root_sha256": review.RECORD_IDENTITY_ROOT_SHA256,
        "identity_payload_pointer_root_sha256": (
            review.IDENTITY_PAYLOAD_POINTER_ROOT_SHA256
        ),
        "maximum_canonical_payload_bytes": 2_124_270,
        "original_pointer_set_sha256": review.ORIGINAL_POINTER_ROOT_SHA256,
        "root_field_record_count": 4_152,
        "total_record_count": 4_691,
        "workstream_record_count": 539,
    }
    authorization = artifact["authorization"]
    assert authorization["scientific_target"] == review.SCIENTIFIC_TARGET
    assert authorization["maintenance_target"] == review.MAINTENANCE_TARGET


def test_v1_review_lean_certificate_binds_rejection_and_nonauthorization() -> None:
    lean = (
        review.REPO_ROOT
        / "formal/toe_formal/ToeFormal/Release/"
        "LoopControlRegistryShardingExecutionReadinessPacketV1IndependentReview.lean"
    ).read_text(encoding="utf-8")
    assert EXPECTED_REVIEW_SHA256 in lean
    assert review.EXPECTED_SHA256[review.PACKET_REL] in lean
    assert review.SCIENTIFIC_TARGET in lean
    assert review.MAINTENANCE_TARGET in lean
    assert "correctiveV1PreparationAccepted : Bool := false" in lean
    assert "prototypeSelectionAuthorized : Bool := false" in lean
    assert "migrationExecutionAuthorized : Bool := false" in lean
    assert "cutoverAuthorized : Bool := false" in lean
