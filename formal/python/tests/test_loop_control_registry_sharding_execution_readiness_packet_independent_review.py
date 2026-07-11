from __future__ import annotations

import hashlib
import json
import subprocess
import sys

from formal.python.tools import (
    loop_control_registry_sharding_execution_readiness_packet_independent_review
    as review,
)


EXPECTED_REVIEW_SHA256 = (
    "7361b386c68590e776b4dcf354264c3ac07217d8dbabe56f722e8cb5c2b97982"
)


def _artifact() -> dict:
    return json.loads(review.OUTPUT_PATH.read_text(encoding="utf-8"))


def test_review_is_deterministic_from_two_commit_preparation_boundary() -> None:
    raw = review.canonical_json_bytes(review.build_review())
    assert review.OUTPUT_PATH.read_bytes() == raw
    assert hashlib.sha256(raw).hexdigest() == EXPECTED_REVIEW_SHA256
    immutable = _artifact()["immutable_input_review"]
    assert immutable["original_preparation_commit"] == review.PREPARATION_COMMIT
    assert immutable["corrected_review_boundary_commit"] == (
        review.CORRECTED_REVIEW_BOUNDARY_COMMIT
    )
    correction = immutable["portability_correction"]
    assert correction["changed_path_count"] == 1
    assert correction["only_changed_path"] == review.PREPARATION_TEST_REL
    assert correction["repair"] == (
        "HARDCODED_WORKSPACE_VENV_INTERPRETER_REPLACED_BY_SYS_EXECUTABLE"
    )


def test_review_cli_check_is_read_only() -> None:
    before = review.OUTPUT_PATH.read_bytes()
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "formal.python.tools."
            "loop_control_registry_sharding_execution_readiness_packet_independent_review",
            "--check",
        ],
        cwd=review.REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, result.stderr
    assert review.OUTPUT_PATH.read_bytes() == before


def test_review_rejects_v0_as_a_contract_and_retains_only_historical_evidence() -> None:
    artifact = _artifact()
    assert artifact["status"] == (
        "REJECTED_EXECUTION_READINESS_PREPARATION_CONTRACT_V0_"
        "HISTORICAL_PREPARATION_EVIDENCE_ONLY_VERSIONED_CORRECTIVE_SUCCESSOR_REQUIRED_"
        "NO_PROTOTYPE_MIGRATION_OR_CUTOVER_AUTHORITY"
    )
    assert artifact["accepted_scope"] == {
        "closed_schema_preparation_contract": False,
        "execution_protocol_preparation_contract": False,
        "historical_preparation_evidence": True,
        "packet_acceptance": False,
        "prototype_selection": False,
        "registry_cutover": False,
        "registry_migration_execution_readiness": False,
    }
    assert all(
        value is False
        for key, value in artifact["authorization"].items()
        if key.endswith("authorized") or key.endswith("selected")
    )


def test_review_independently_validates_ten_closed_schemas() -> None:
    schema = _artifact()["schema_review"]
    assert schema == {
        "draft": "2020-12",
        "empty_or_unconstrained_slot_count": 0,
        "metaschema_validation_passed": True,
        "object_schema_count": 47,
        "recursive_closure_error_count": 0,
        "schema_count": 10,
        "strict_parser_contract_present": True,
    }
    parser = _artifact()["strict_parser_review"]
    assert parser["review_probe_count"] == 7
    assert parser["review_probes_passed"] is True
    assert parser["production_strict_parser_present"] is False


def test_review_reproduces_v1_records_roots_and_targets() -> None:
    record = _artifact()["record_and_authority_review"]
    assert record["root_field_record_count"] == 4_152
    assert record["workstream_record_count"] == 539
    assert record["total_record_count"] == 4_691
    assert record["record_id_collision_count"] == 0
    assert record["authority_commitment_sha256"] == review.EXPECTED_ROOTS[
        "authority_commitment_sha256"
    ]
    assert record["full_record_identity_root_sha256"] == review.EXPECTED_ROOTS[
        "full_record_identity_root_sha256"
    ]
    assert record["identity_payload_pointer_root_sha256"] == review.EXPECTED_ROOTS[
        "identity_payload_pointer_root_sha256"
    ]
    assert record["original_pointer_set_sha256"] == review.EXPECTED_ROOTS[
        "original_pointer_set_sha256"
    ]
    assert record["targets_reproduced_from_legacy_and_maintenance_authority"] is True


def test_review_matches_all_52_controls_and_four_caller_selected_profiles() -> None:
    controls = _artifact()["control_harness_review"]
    assert controls["control_count"] == 52
    assert controls["controls_executed"] is False
    assert controls["candidate_selected_mode_present"] is False
    assert controls["distinct_positive_baseline_count"] == 4
    assert controls["exact_v1_control_identity_and_error_mapping"] is True
    assert controls["profile_counts"] == {
        "CUTOVER_ELIGIBILITY": 1,
        "PROTOTYPE_INTEGRITY": 47,
        "SHADOW_PARITY": 2,
        "WRITE_SAFETY": 2,
    }
    assert controls["special_profile_assignments"] == {
        "REGISTRY-V1-NC-041": "WRITE_SAFETY",
        "REGISTRY-V1-NC-042": "WRITE_SAFETY",
        "REGISTRY-V1-NC-044": "CUTOVER_ELIGIBILITY",
        "REGISTRY-V1-NC-045": "SHADOW_PARITY",
        "REGISTRY-V1-NC-046": "SHADOW_PARITY",
    }


def test_review_adversarially_demonstrates_the_three_blocking_contract_defects() -> None:
    adversarial = _artifact()["adversarial_contract_review"]
    assert adversarial["cutover_shadow_reader_requirement_conflict"] is True
    assert adversarial["history_payload_cross_field_false_acceptance"] is True
    assert adversarial["path_false_acceptances"] == [
        "/absolute/path.json",
        "//server/share/registry.json",
    ]
    assert adversarial["history_payload_required_runtime_checks_absent"] == [
        "STRICT_BASE64_DECODE",
        "DECODED_SIZE_EQUALS_PAYLOAD_SIZE_BYTES",
        "DECODED_SHA256_EQUALS_PAYLOAD_SHA256",
        "DECODED_KIND_EQUALS_PAYLOAD_KIND",
        "RECOMPUTED_RECORD_ID_EQUALS_RECORD_ID",
    ]


def test_review_demonstrates_report_decision_invariant_false_acceptances() -> None:
    adversarial = _artifact()["adversarial_contract_review"]
    assert adversarial["validation_report_cross_field_false_acceptance"] is True
    assert adversarial["harness_report_cross_field_false_acceptance"] is True


def test_review_preserves_consumer_and_byte_custody_obligations() -> None:
    consumer = _artifact()["consumer_review"]
    assert consumer["baseline_consumer_count"] == 496
    assert consumer["baseline_treated_as_eternal_current_count"] is False
    assert consumer["fresh_full_tree_rescan_required"] is True
    assert consumer["structured_added_removed_changed_delta_required"] is True
    assert consumer["unclassified_current_consumer_count_allowed"] == 0
    custody = _artifact()["custody_review"]
    assert custody["source_registry_sha256"] == review.EXPECTED_ACCEPTED_SHA256[
        review.REGISTRY_REL
    ]
    assert custody["source_registry_size_bytes"] == 52_340_650
    assert custody["legacy_byte_identity_required"] is True
    assert custody["semantic_equivalence_alone_sufficient"] is False
    assert custody["custody_payload_created"] is False


def test_unpinned_validator_is_a_prototype_blocker_not_packet_defect() -> None:
    artifact = _artifact()
    blocker = artifact["validator_engine_blocker"]
    assert blocker == {
        "direct_requirements_active_lock_present": False,
        "direct_requirements_ci_lock_present": False,
        "observed_review_runtime_version": "4.26.0",
        "packet_defect": False,
        "prototype_selection_blocked": True,
        "required_exact_version": "4.26.0",
    }
    findings = artifact["findings"]
    assert [row["finding_id"] for row in findings] == [
        "REGISTRY-READINESS-REVIEW-001",
        "REGISTRY-READINESS-REVIEW-002",
        "REGISTRY-READINESS-REVIEW-003",
        "REGISTRY-READINESS-REVIEW-004",
        "REGISTRY-READINESS-REVIEW-005",
    ]
    assert [row["severity"] for row in findings] == [
        "HIGH",
        "HIGH",
        "HIGH",
        "MEDIUM",
        "HIGH",
    ]
    assert all(row["packet_defect"] is True for row in findings[:4])
    assert findings[4]["packet_defect"] is False


def test_review_finds_no_production_or_prototype_artifacts_and_no_authorization() -> None:
    artifact = _artifact()
    assert artifact["path_absence_review"] == {
        "forbidden_path_count": 7,
        "production_and_prototype_paths_absent": True,
    }
    nonauthorization = artifact["nonauthorization_review"]
    assert nonauthorization["all_false"] is True
    assert nonauthorization["nonauthorization_boolean_count"] == 38
    assert sum(nonauthorization["group_counts"].values()) == 38


def test_review_lean_certificate_binds_acceptance_and_all_nonauthorizations() -> None:
    lean_path = (
        review.REPO_ROOT
        / "formal/toe_formal/ToeFormal/Release/"
        "LoopControlRegistryShardingExecutionReadinessPacketIndependentReview.lean"
    )
    lean = lean_path.read_text(encoding="utf-8")
    assert EXPECTED_REVIEW_SHA256 in lean
    assert review.PREPARATION_COMMIT in lean
    assert review.CORRECTED_REVIEW_BOUNDARY_COMMIT in lean
    assert review.EXPECTED_PREPARATION_SHA256[review.PACKET_REL] in lean
    assert review.SCIENTIFIC_TARGET in lean
    assert review.MAINTENANCE_TARGET in lean
    assert "historicalPreparationEvidenceRetained : Bool := true" in lean
    assert "preparationContractAccepted : Bool := false" in lean
    assert "prototypeSelectionAccepted : Bool := false" in lean
    assert "migrationExecutionReadinessAccepted : Bool := false" in lean
    assert "registryCutoverAccepted : Bool := false" in lean
