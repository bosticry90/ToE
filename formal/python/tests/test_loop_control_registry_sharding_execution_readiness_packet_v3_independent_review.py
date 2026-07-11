from __future__ import annotations

import hashlib
import json
import subprocess
import sys

from formal.python.tools import (
    loop_control_registry_sharding_execution_readiness_packet_v3_independent_review
    as review,
)


EXPECTED_REVIEW_SHA256 = (
    "07353bc1c0d379518344aa16c25080fefb6dd9c1527cad4accb64216b15adae0"
)


def _artifact() -> dict:
    return json.loads(review.OUTPUT_PATH.read_text(encoding="utf-8"))


def test_v3_review_is_deterministic_from_exact_preparation_commit() -> None:
    raw = review.canonical_json_bytes(review.build_review())
    assert review.OUTPUT_PATH.read_bytes() == raw
    assert hashlib.sha256(raw).hexdigest() == EXPECTED_REVIEW_SHA256
    assert _artifact()["reviewed_commit"] == review.SOURCE_COMMIT


def test_v3_review_cli_check_is_read_only() -> None:
    before = review.OUTPUT_PATH.read_bytes()
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "formal.python.tools.loop_control_registry_sharding_execution_readiness_packet_v3_independent_review",
            "--check",
        ],
        cwd=review.REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, result.stderr
    assert review.OUTPUT_PATH.read_bytes() == before


def test_v3_review_accepts_only_the_bounded_preparation_contract() -> None:
    artifact = _artifact()
    assert artifact["status"] == (
        "ACCEPTED_CORRECTIVE_V3_PREPARATION_CONTRACT_NO_PRODUCTION_"
        "VALIDATOR_HARNESS_PROTOTYPE_MIGRATION_CUTOVER_OR_AUTHORITY"
    )
    authorization = artifact["authorization"]
    assert authorization["corrective_v3_preparation_accepted"] is True
    assert authorization["registry_migration_execution_readiness_accepted"] is False
    assert authorization["production_artifact_validators_implemented_or_executed"] is False
    assert authorization["prototype_selection_authorized"] is False
    assert authorization["migration_execution_authorized"] is False
    assert authorization["cutover_authorized"] is False
    assert authorization["unit_ledger_execution_authorized"] is False


def test_v3_review_reproduces_contract_scale_and_source_fixture() -> None:
    evidence = _artifact()["acceptance_evidence"]
    assert evidence == {
        "closed_schema_count": 10,
        "consumer_path_count": 496,
        "control_error_pair_count": 60,
        "field_semantic_profile_mapping_count": 33,
        "full_profile_baselines_executed": False,
        "positive_fixture_count": 5,
        "readiness_regression_count": 8,
        "reviewed_input_count": 11,
        "schema_profile_count": 7,
        "source_backed_history_record_id": review.EXPECTED_RECORD_ID,
    }


def test_v3_review_binds_every_input_by_sha_and_git_blob() -> None:
    assert set(review.EXPECTED_SHA256) == set(review.EXPECTED_GIT_BLOBS)
    assert len(review.EXPECTED_SHA256) == 11
    for relative, expected_sha in review.EXPECTED_SHA256.items():
        raw = review._git_blob(relative)
        assert hashlib.sha256(raw).hexdigest() == expected_sha
        assert review._git_blob_oid(relative) == review.EXPECTED_GIT_BLOBS[relative]


def test_v3_review_keeps_targets_and_historical_path_absence_frozen() -> None:
    authorization = _artifact()["authorization"]
    assert authorization["scientific_target"] == review.SCIENTIFIC_TARGET
    assert authorization["maintenance_target"] == review.MAINTENANCE_TARGET
    assert authorization["scientific_target_rotation_authorized"] is False
    assert authorization["maintenance_target_rotation_authorized"] is False
    for relative in review.FORBIDDEN_PATHS:
        assert not review._path_exists_at_source_commit(relative)


def test_v3_review_retains_future_implementation_obligations() -> None:
    artifact = _artifact()
    findings = {row["finding_id"]: row for row in artifact["independent_findings"]}
    assert len(findings) == 3
    assert findings["REGISTRY-READINESS-V3-REVIEW-001"]["status"] == (
        "CLOSED_FOR_PREPARATION_CONTRACT"
    )
    assert findings["REGISTRY-READINESS-V3-REVIEW-002"]["status"] == (
        "CLOSED_FOR_PREPARATION_CONTRACT"
    )
    assert findings["REGISTRY-READINESS-V3-REVIEW-003"]["status"] == (
        "OPEN_FUTURE_IMPLEMENTATION_OBLIGATION_NOT_A_V3_DEFECT"
    )
    assert len(artifact["residual_obligations"]) == 5
    assert "EXECUTE_52_PLUS_8_CONTROL_HARNESS_AGAINST_READ_ONLY_PROTOTYPE" in artifact[
        "residual_obligations"
    ]


def test_v3_review_lean_certificate_binds_acceptance_and_nonauthorization() -> None:
    lean = (
        review.REPO_ROOT
        / "formal/toe_formal/ToeFormal/Release/"
        "LoopControlRegistryShardingExecutionReadinessPacketV3IndependentReview.lean"
    ).read_text(encoding="utf-8")
    assert EXPECTED_REVIEW_SHA256 in lean
    assert review.EXPECTED_SHA256[review.PACKET_REL] in lean
    assert review.EXPECTED_SHA256[review.SCHEMA_REL] in lean
    assert review.EXPECTED_SHA256[review.PROTOCOL_REL] in lean
    assert review.SCIENTIFIC_TARGET in lean
    assert review.MAINTENANCE_TARGET in lean
    assert "correctiveV3PreparationAccepted : Bool := true" in lean
    assert "migrationExecutionReadinessAccepted : Bool := false" in lean
    assert "prototypeSelectionAuthorized : Bool := false" in lean
    assert "migrationExecutionAuthorized : Bool := false" in lean
    assert "cutoverAuthorized : Bool := false" in lean
