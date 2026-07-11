from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    loop_control_registry_sharding_guardrail_independent_review as review,
)


EXPECTED_REVIEW_SHA256 = (
    "5e43181b11a4d302a301bd915a43a40636bf947d93edc9f327e9c0a7beceb485"
)
EXPECTED_ACCEPTED_INVALID_LAYOUTS = [
    "authority_drift_with_rebound_fingerprint",
    "broken_current_index_pointer",
    "changed_history_with_rebound_index",
    "duplicate_shard_id",
    "nan_history_with_rebound_index",
    "noncanonical_jsonl",
    "oversized_current_projection",
    "two_maintenance_targets",
]


def _artifact() -> dict:
    return json.loads(review.OUTPUT_PATH.read_text(encoding="utf-8"))


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_independent_review_artifact_is_deterministic_and_current() -> None:
    expected = review.canonical_json_bytes(review.build_review())
    assert review.OUTPUT_PATH.read_bytes() == expected
    assert hashlib.sha256(expected).hexdigest() == EXPECTED_REVIEW_SHA256


def test_review_reproduces_the_frozen_debt_inventory_without_silent_rebaseline() -> None:
    artifact = _artifact()
    reproduced = artifact["independent_baseline_reproduction"]
    assert reproduced["retired_assertion_count"] == 197
    assert reproduced["retired_assertion_unique_nodeid_count"] == 197
    assert reproduced["axiom_count"] == 59
    assert reproduced["blocking_axiom_count"] == 22
    assert reproduced["opaque_candidate_count"] == 46
    assert reproduced["snapshot_path_count"] == 59
    assert reproduced["snapshot_duplicate_group_count"] == 14
    assert reproduced["snapshot_redundant_worktree_bytes"] == 424_292_098

    # The baseline remains accepted for its headline inventory, while a versioned
    # successor must repair its weak declaration-line hashes.
    assert reproduced["empty_axiom_statement_line_hash_count"] == 50
    assert reproduced["empty_opaque_statement_line_hash_count"] == 20

    inputs = artifact["input_artifacts"]
    assert {row["reviewed_commit"] for row in inputs} == {
        review.BASELINE_COMMIT,
        review.GUARDRAIL_COMMIT,
    }
    assert len(inputs) == 15
    assert all(
        row["review_source"] in {"immutable_git_blob", "immutable_git_tree_projection"}
        for row in inputs
    )
    assert all(row["working_copy_state_not_used_for_regeneration"] for row in inputs)
    assert artifact["comparison_results"]["baseline_counts_and_identity_sets"][
        "matches"
    ] is True
    source_bindings = artifact["comparison_results"]["baseline_embedded_source_hashes"]
    assert source_bindings["matches"] is False
    assert source_bindings["mismatches"] == {
        "retirements_source_ledger_sha256": {
            "expected": "78c534f097205dcb117ad34161ecf4357a6a434a5ed02dd8bdaacb782ba58691",
            "observed": "56e98643db2b891e7dbb73211cb88e02721308c43dd6ad3becf6584d70cc5592",
        }
    }
    assert artifact["accepted_scope"][
        "baseline_embedded_source_hashes_match_reviewed_commit_blobs"
    ] is False


def test_review_reproduces_registry_accounting_but_refutes_byte_round_trip() -> None:
    accounting = _artifact()["independent_registry_accounting"]
    assert accounting["root_field_record_count"] == 4_152
    assert accounting["workstream_record_count"] == 539
    assert accounting["total_history_record_count"] == 4_691
    assert accounting["record_id_count"] == 4_691
    assert accounting["record_id_unique_count"] == 4_691
    assert accounting["legacy_registry_sha256"] == (
        "eda451133e8bbfe1ba0e815b29735f874e8b33e61d7fc5085999c4ba38df0543"
    )
    assert accounting["direct_object_reserialization_byte_identical"] is True
    assert accounting["record_jsonl_round_trip_reconstruction_semantically_equal"] is True
    assert accounting["record_jsonl_round_trip_reconstruction_byte_identical"] is False
    assert accounting["record_jsonl_round_trip_sha256"] == (
        "0913423f3eb5d2d56419fe4a2c648152e846d3205ee7f849f99c29ae27bf1118"
    )
    assert accounting["record_jsonl_round_trip_first_difference_offset"] == 367_556
    assert accounting["record_jsonl_round_trip_reconstructed_size_bytes"] == 52_340_650
    assert accounting["source_size_bytes"] == 52_340_650
    assert accounting["nested_workstream_like_object_count_outside_catalog"] == 4
    scope = _artifact()["accepted_scope"]
    assert scope["top_level_record_arithmetic_reproduced"] is True
    assert scope["nested_workstream_semantic_classification_complete"] is False


def test_review_records_each_adversarial_false_acceptance() -> None:
    artifact = _artifact()
    probes = artifact["adversarial_probe_results"]
    assert probes["accepted_invalid_layout_count"] == 8
    assert probes["accepted_invalid_layouts"] == EXPECTED_ACCEPTED_INVALID_LAYOUTS
    assert set(probes["results"].values()) == {"ACCEPTED_INVALID_LAYOUT"}
    assert set(probes["probe_expectations"].values()) == {"REJECT_INVALID_LAYOUT"}
    assert probes["reviewed_validator_blob_sha256"] == (
        "990df444a2ff603ec3571bd6b9c693a7b7a328c72b445d036180f187f7caed92"
    )

    controls = artifact["negative_control_review"]
    assert controls["current_control_count"] == 24
    assert controls["review_outcome"] == (
        "CONTROL_SET_NOT_COMPLETE_ENOUGH_FOR_MIGRATION_EXECUTION"
    )
    assert {
        "changed_historical_record_against_external_frozen_source",
        "authority_change_with_rebound_candidate_fingerprint",
        "broken_current_history_index_pointer",
        "forged_or_unrecomputed_record_id",
        "nan_or_infinity",
        "oversized_current_projection",
        "write_attempt_against_closed_shard",
    }.issubset(controls["missing_or_not_independently_enforced_controls"])


def test_review_finds_consumer_inventory_scope_gap_without_rewriting_v0_counts() -> None:
    inventory = _artifact()["consumer_inventory_review"]
    assert inventory["python_literal_path_count"] == 467
    assert inventory["minimum_known_python_reader_union_count"] == 490
    assert inventory["literal_path_count_all_tracked_file_types_including_monolith"] == 492
    assert inventory["external_literal_reference_path_count"] == 491
    assert inventory["external_non_python_literal_reference_path_count"] == 24
    assert inventory["dynamic_and_cross_language_consumer_completeness_proved"] is False
    assert len(inventory["identified_nonliteral_reader_paths_missing_from_487_union"]) == 3


def test_review_disposition_fails_closed_and_preserves_both_targets() -> None:
    artifact = _artifact()
    decision = artifact["review_decision"]
    assert artifact["status"] == (
        "REVIEW_REJECTS_MIGRATION_EXECUTION_READINESS_"
        "VERSIONED_CORRECTIVE_GUARDRAIL_REQUIRED"
    )
    assert decision["baseline_commit_decision"] == (
        "ACCEPTED_COUNTS_AND_IDENTITY_SETS_ONLY_"
        "VERSIONED_SOURCE_BINDING_AND_STATEMENT_HASH_CORRECTION_REQUIRED"
    )
    assert decision["guardrail_commit_decision"] == (
        "ACCEPTED_AS_PREPARATION_EVIDENCE_REJECTED_AS_MIGRATION_EXECUTION_AUTHORITY"
    )
    assert decision["scientific_target"] == review.SCIENTIFIC_TARGET
    assert decision["maintenance_target"] == review.MAINTENANCE_TARGET
    assert decision["scientific_target_rotated"] is False
    assert decision["maintenance_target_rotated"] is False
    assert decision["registry_migration_execution_authorized"] is False
    assert decision["recommended_corrective_target"] == review.RECOMMENDED_CORRECTIVE_TARGET
    assert decision["recommended_corrective_target_selected"] is False
    assert all(value is False for value in artifact["boundary"].values())

    severity_counts: dict[str, int] = {}
    for finding in artifact["findings"]:
        severity = finding["severity"]
        severity_counts[severity] = severity_counts.get(severity, 0) + 1
    assert severity_counts == {"CRITICAL": 2, "HIGH": 7, "MEDIUM": 2}


def test_lean_review_certificate_binds_rejection_hash_and_nonauthorization() -> None:
    lean_path = (
        review.REPO_ROOT
        / "formal/toe_formal/ToeFormal/Release/LoopControlRegistryShardingGuardrailIndependentReview.lean"
    )
    text = lean_path.read_text(encoding="utf-8")
    assert _sha256(review.OUTPUT_PATH) == EXPECTED_REVIEW_SHA256
    assert EXPECTED_REVIEW_SHA256 in text
    assert review.BASELINE_COMMIT in text
    assert review.GUARDRAIL_COMMIT in text
    assert review.SCIENTIFIC_TARGET in text
    assert review.MAINTENANCE_TARGET in text
    assert review.RECOMMENDED_CORRECTIVE_TARGET in text
    assert "migrationExecutionAuthorized : Bool := false" in text
    assert "correctiveTargetSelected : Bool := false" in text
    assert "proposedJsonlRoundTripByteIdentical : Bool := false" in text
