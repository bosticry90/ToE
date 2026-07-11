from __future__ import annotations

import hashlib
import json

from formal.python.tools import (
    loop_control_registry_sharding_execution_readiness_packet_v2_independent_review
    as review,
)


EXPECTED_REVIEW_SHA256 = (
    "cf1e9bdc8617824f4ab2a93d9463912665a090aa5c80f2e17589436d1df98390"
)


def _artifact() -> dict:
    return json.loads(review.OUTPUT_PATH.read_text(encoding="utf-8"))


def test_v2_review_is_deterministic_from_immutable_corrective_commit() -> None:
    raw = review.canonical_json_bytes(review.build_review())
    assert review.OUTPUT_PATH.read_bytes() == raw
    assert hashlib.sha256(raw).hexdigest() == EXPECTED_REVIEW_SHA256


def test_v2_review_rejects_preparation_and_every_execution_authority() -> None:
    artifact = _artifact()
    assert artifact["status"] == (
        "REJECTED_CORRECTIVE_V2_PREPARATION_CONTRACT_INVALID_POSITIVE_FIXTURE_"
        "NONCONCRETE_MUTATION_VECTORS_AND_ISSUE_MAPPING_NO_EXECUTION_OR_AUTHORITY"
    )
    authorization = artifact["authorization"]
    assert authorization["corrective_v2_preparation_accepted"] is False
    assert authorization["prototype_selection_authorized"] is False
    assert authorization["migration_execution_authorized"] is False
    assert authorization["cutover_authorized"] is False
    assert authorization["scientific_target_rotation_authorized"] is False
    assert authorization["maintenance_target_rotation_authorized"] is False
    assert authorization["versioned_v3_required"] is True


def test_v2_review_accepts_only_reproduced_bounded_corrections() -> None:
    accepted = _artifact()["accepted_corrections"]
    assert all(accepted.values())
    assert accepted["all_496_frozen_consumer_paths_validate"] is True
    assert accepted["prototype_absolute_unc_and_traversal_paths_rejected"] is True
    assert accepted["both_control_id_namespaces_validate_in_shared_issue_schema"] is True
    assert accepted["profile_branches_counts_and_roots_exact"] is True
    assert accepted["record_and_root_algorithms_reproduce_frozen_roots"] is True
    assert accepted["original_52_migration_controls_unchanged"] is True
    assert accepted["explicit_shadow_nonmigration_and_noncutover_fields_present"] is True


def test_v2_review_reproduces_invalid_rc002_positive_fixture() -> None:
    finding = _artifact()["findings"][0]
    assert finding["finding_id"] == "REGISTRY-READINESS-V2-REVIEW-001"
    probe = finding["probe"]
    assert probe == {
        "after": "Zh==",
        "after_decoded_utf8": "f",
        "before": "Zg==",
        "before_decoded_utf8": "f",
        "positive_fixture_json_valid": False,
        "recommended_after": "bnVsbB==",
        "recommended_before": "bnVsbA==",
    }
    assert finding["severity"] == "HIGH"
    assert finding["status"] == "OPEN_BLOCKS_V2_PACKET_ACCEPTANCE_AND_ALL_EXECUTION"


def test_v2_review_rejects_symbolic_rc007_and_rc008_vectors() -> None:
    finding = _artifact()["findings"][1]
    assert finding["finding_id"] == "REGISTRY-READINESS-V2-REVIEW-002"
    assert finding["symbolic_mutation_vectors"] == {
        "REGISTRY-READINESS-V1-RC-007": [["ONE_VALID_ISSUE"]],
        "REGISTRY-READINESS-V1-RC-008": [
            "BASELINE_SHA256",
            "DIFFERENT_SHA256",
        ],
    }
    assert finding["severity"] == "HIGH"


def test_v2_review_keeps_secondary_interface_and_shadow_drift_explicit() -> None:
    findings = {row["finding_id"]: row for row in _artifact()["findings"]}
    assert len(findings) == 6
    assert sum(row["severity"] == "HIGH" for row in findings.values()) == 3
    assert sum(row["severity"] == "MEDIUM" for row in findings.values()) == 3
    assert findings["REGISTRY-READINESS-V2-REVIEW-003"][
        "stale_passed_contract"
    ] == "TRUE_ONLY_WHEN_ERRORS_EMPTY"
    assert "<run_id>" in findings["REGISTRY-READINESS-V2-REVIEW-004"][
        "trace_output"
    ]
    assert findings["REGISTRY-READINESS-V2-REVIEW-005"][
        "issue_schema_accepts_mismatched_control_error_pair"
    ] is True
    assert findings["REGISTRY-READINESS-V2-REVIEW-005"][
        "mapping_invariant_present"
    ] is False
    assert findings["REGISTRY-READINESS-V2-REVIEW-006"][
        "resolved_registry_path_is_prototype_typed"
    ] is True


def test_v2_review_reproduces_record_roots_and_preserves_targets() -> None:
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


def test_v2_review_lean_certificate_binds_rejection_and_nonauthorization() -> None:
    lean = (
        review.REPO_ROOT
        / "formal/toe_formal/ToeFormal/Release/"
        "LoopControlRegistryShardingExecutionReadinessPacketV2IndependentReview.lean"
    ).read_text(encoding="utf-8")
    assert EXPECTED_REVIEW_SHA256 in lean
    assert review.EXPECTED_SHA256[review.PACKET_REL] in lean
    assert review.SCIENTIFIC_TARGET in lean
    assert review.MAINTENANCE_TARGET in lean
    assert "correctiveV2PreparationAccepted : Bool := false" in lean
    assert "prototypeSelectionAuthorized : Bool := false" in lean
    assert "migrationExecutionAuthorized : Bool := false" in lean
    assert "cutoverAuthorized : Bool := false" in lean
