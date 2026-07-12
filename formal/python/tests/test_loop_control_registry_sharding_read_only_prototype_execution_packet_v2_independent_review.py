from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess

from formal.python.tools import (
    loop_control_registry_sharding_read_only_prototype_execution_packet_v2_independent_review
    as review,
)


REPO_ROOT = review.REPO_ROOT


def _artifact() -> dict:
    return json.loads(review.OUTPUT_PATH.read_text(encoding="utf-8"))


def _contract() -> dict:
    return review._strict_json(
        review._git_blob(review.PREPARATION_COMMIT, review.CONTRACT_REL)
    )


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def test_blocked_review_is_canonical_and_exactly_hash_bound() -> None:
    observed = review.OUTPUT_PATH.read_bytes()
    assert observed == review.canonical_json_bytes(_artifact())
    assert _sha256(observed) == (
        "5b1505fb722121329a3d0d08dc9fe8d10674ede0ccce9c1b7a2ffed1ef7d3cd6"
    )


def test_review_binds_immutable_preparation_commit_tree_packet_and_contract() -> None:
    artifact = _artifact()
    assert artifact["preparation_commit"] == review.PREPARATION_COMMIT
    assert artifact["preparation_commit_parent"] == review.SOURCE_COMMIT
    assert artifact["preparation_tree"] == review.PREPARATION_TREE
    assert artifact["packet_sha256"] == review.PACKET_SHA256
    assert artifact["contract_bundle_sha256"] == review.CONTRACT_SHA256


def test_all_preparation_inputs_match_exact_git_objects() -> None:
    observed = review._preparation_input_evidence()
    assert observed == _artifact()["reviewed_inputs"]
    assert set(observed) == set(review.PREPARATION_INPUTS)


def test_packet_and_contract_are_strict_canonical_finite_json() -> None:
    for relative in (review.PACKET_REL, review.CONTRACT_REL):
        raw = review._git_blob(review.PREPARATION_COMMIT, relative)
        assert review.canonical_json_bytes(review._strict_json(raw)) == raw


def test_independent_schema_walk_finds_111_annotated_edges_and_ten_omissions() -> None:
    result = review._graph_review(_contract())
    assert result["independently_derived_edge_count"] == 111
    assert result["contract_edge_count"] == 111
    assert result["unannotated_hash_bearing_field_count"] == 10
    assert {
        (row["schema_name"], row["schema_field_path"])
        for row in result["unannotated_hash_bearing_fields"]
    } == {
        ("candidate_consumer_map", "/consumers/*/consumer_id"),
        ("current_projection", "/active_scientific_workstream/record_id"),
        ("history_index", "/shards/*/first_record_id"),
        ("history_index", "/shards/*/last_record_id"),
        ("history_index", "/shards/*/shard_id"),
        ("history_shard_record", "/record_id"),
        ("independent_review_consumer_inventory", "/consumers/*/consumer_id"),
        ("preflight_consumer_inventory", "/consumers/*/consumer_id"),
        ("runtime_trace_event", "/consumer_id"),
        ("runtime_trace_event", "/trace_id"),
    }
    assert result["self_edge_count"] == 0
    assert result["reciprocal_edge_count"] == 0
    assert result["later_or_same_phase_edge_count"] == 0
    assert result["complete_branch_topological_sort_succeeds"] is True
    assert result["post_generation_blocked_branch_topological_sort_succeeds"] is True


def test_fourteen_dynamic_candidate_edges_have_real_requiredness_mismatch() -> None:
    contract = _contract()
    unannotated = []
    derived = review.derive_schema_edge_table(
        contract,
        reject_unannotated=False,
        unannotated=unannotated,
    )
    assert len(unannotated) == 10
    declared = contract["reviewed_schema_hash_edge_table"]["rows"]
    omitted = [row for row in derived if row not in declared]
    invented = [row for row in declared if row not in derived]
    assert len(omitted) == len(invented) == 14
    assert {
        (row["containing_artifact_type"], row["schema_field_path"])
        for row in omitted + invented
    } == {("RUNTIME_MANIFEST", "/candidate_artifacts/*/sha256")}
    assert {row["required_optional_status"] for row in omitted} == {
        "CONDITIONAL_OR_OPTIONAL"
    }
    assert {row["required_optional_status"] for row in invented} == {"REQUIRED"}
    result = _artifact()["graph_review"]
    assert result["independently_derived_edge_root_sha256"] == (
        "1db029814955bab15a248aa2bb9f61a67a2faa3a4c1fcaca4169878756ff989c"
    )
    assert result["contract_edge_root_sha256"] == review.EDGE_ROOT_SHA256
    assert result["declared_contract_and_review_derived_rows_equal"] is False


def test_frozen_generator_does_not_reproduce_frozen_artifacts() -> None:
    result = _artifact()["detached_clean_checkout_determinism_review"]
    assert result["detached_clean_checkout_commit"] == review.PREPARATION_COMMIT
    assert result["detached_regeneration_count"] == 2
    assert result["regenerations_byte_identical_to_each_other"] is True
    assert result["regenerations_equal_committed_artifacts"] is False
    assert result["regenerated_packet_sha256"] == review.REGENERATED_PACKET_SHA256
    assert result["regenerated_contract_sha256"] == review.REGENERATED_CONTRACT_SHA256
    assert result["committed_packet_sha256"] == review.PACKET_SHA256
    assert result["committed_contract_sha256"] == review.CONTRACT_SHA256
    assert result["committed_tree"] == review.PREPARATION_TREE
    assert result["committed_parent"] == review.SOURCE_COMMIT
    assert all(
        row["detached_head"] == review.PREPARATION_COMMIT
        and row["prototype_root_created"] is False
        and set(row["changed_paths"]) == {review.CONTRACT_REL, review.PACKET_REL}
        for row in result["regeneration_runs"]
    )


def test_independent_source_and_preparation_consumer_rescans_are_exact() -> None:
    result = review._consumer_review(_contract())
    source = result["legacy_literal_source_commit_scan"]
    preparation = result["legacy_literal_preparation_commit_scan"]
    assert source["callsite_identity_count"] == 584
    assert source["unique_path_count"] == 522
    assert source["runtime_required_count"] == 23
    assert source["nonruntime_count"] == 561
    assert preparation["callsite_identity_count"] == 592
    assert preparation["unique_path_count"] == 524
    assert preparation["runtime_required_count"] == 28
    assert preparation["nonruntime_count"] == 564
    assert preparation["added_path_count"] == 28
    assert preparation["removed_path_count"] == 0
    assert preparation["baseline_changed_path_count"] == 3


def test_preparation_delta_is_non_normative_and_identity_sets_are_not_subtracted() -> None:
    result = _artifact()["consumer_inventory_review"]
    assert result["preparation_only_identity_count"] == 19
    assert result["source_only_identity_count"] == 11
    assert result["preparation_only_consumer_paths"] == [
        review.CONTRACT_REL,
        review.GENERATOR_REL,
    ]
    assert result["review_commit_equals_contract_model_source_commit"] is False
    assert result["contract_historical_scan_is_marked_non_normative"] is True
    assert result["source_witness_identity_root_matches_frozen_evidence"] is False


def test_executable_inventory_scanner_violates_frozen_algorithm_and_schema() -> None:
    result = _artifact()["consumer_inventory_review"]
    assert result["contract_requires_python_ast_passes"] is True
    assert result["review_scanner_contract_conformant"] is False
    assert result["emitted_mechanisms_are_allowed_by_contract"] is False
    assert result["emitted_row_count_with_schema_forbidden_mechanism"] == 592
    assert result["emitted_discovery_mechanisms"] == [
        "GIT_COMMIT_BLOB_LITERAL_OCCURRENCE",
        "REVIEWED_NONLITERAL_PATH_RULE",
    ]


def test_all_27_frozen_controls_report_exact_isolated_failures() -> None:
    result = _artifact()["control_review"]
    assert result["frozen_control_count"] == 27
    assert result["retained_v1_control_count"] == 12
    assert result["new_v2_control_count"] == 15
    assert result["frozen_control_ids_unique"] is True
    assert result["frozen_results_all_report_isolated_clean_baselines"] is True
    assert result["frozen_results_all_report_intended_code"] is True
    execution = result["detached_frozen_validator_control_test"]
    assert execution["passed"] is True
    assert execution["selected_test_count"] == 1
    assert execution["prototype_root_created"] is False


def test_reviewer_model_probes_are_isolated_but_not_frozen_validator_evidence() -> None:
    rows = review._inventory_probe_results()
    assert len(rows) == 15
    assert len({row["control_id"] for row in rows}) == 15
    assert all(row["isolated_deep_copy"] for row in rows)
    assert all(row["passed"] for row in rows)
    assert all(
        row["expected_error_code"] == row["observed_error_code"] for row in rows
    )
    assert all(
        row["baseline_root_sha256_before"] == row["baseline_root_sha256_after"]
        for row in rows
    )
    assert all(row["subsequent_controls_uncontaminated"] for row in rows)
    assert {row["evidence_scope"] for row in rows} == {
        "REVIEWER_MODEL_ONLY_NOT_FROZEN_VALIDATOR"
    }
    assert _artifact()["control_review"][
        "reviewer_model_probes_are_frozen_validator_evidence"
    ] is False


def test_full_custody_model_accounts_for_every_record_exactly_once() -> None:
    result = review._custody_review(_contract())
    assert result["record_count"] == 4_691
    assert result["root_field_record_count"] == 4_152
    assert result["workstream_record_count"] == 539
    assert result["all_record_ids_unique"] is True
    assert result["all_source_pointers_unique"] is True
    assert result["record_roots_match_schema_constants"] is True


def test_all_fourteen_shards_have_valid_ranges_hashes_and_sizes() -> None:
    result = _artifact()["custody_review"]
    shards = result["shard_descriptors"]
    assert result["shard_count"] == len(shards) == 14
    assert result["shard_ranges_are_contiguous_and_sorted"] is True
    assert sum(row["record_count"] for row in shards) == 4_691
    assert [row["sequence_index"] for row in shards] == list(range(14))
    assert all(0 < row["uncompressed_size_bytes"] <= 5_242_880 for row in shards)
    assert all(len(row["sha256"]) == 64 for row in shards)
    assert all(row["first_record_id"] <= row["last_record_id"] for row in shards)


def test_custody_reconstruction_is_byte_exact_not_semantic_only() -> None:
    result = _artifact()["custody_review"]
    assert result["byte_exact_legacy_reconstruction"] is True
    assert result["registry_sha256"] == review.REGISTRY_SHA256
    assert result["decompressed_sha256"] == review.REGISTRY_SHA256
    assert result["registry_size_bytes"] == result["decompressed_size_bytes"] == 52_340_650


def test_external_source_roots_verify_but_future_root_resolver_is_not_implemented() -> None:
    result = review._external_root_review(_contract())
    assert result["frozen_input_mismatches"] == []
    assert result["implementation_inventory_root_matches"] is True
    assert result[
        "protocol_registry_schema_and_implementation_source_roots_verify"
    ] is True
    assert result["candidate_may_rebind_expected_values"] is False
    assert result["symbolic_roots_explicitly_model_only"] is True
    assert result["production_future_contract_and_review_root_resolver_implemented"] is False


def test_production_paths_remain_the_unchanged_blocked_v0_boundary() -> None:
    result = review._implementation_review(_contract())
    assert result["authorized_implementation_path_count"] == 4
    assert all(
        row["source_and_preparation_bytes_equal"]
        for row in result["authorized_implementation_paths"]
    )
    assert result["blocked_v0_contract_binding_still_present"] is True
    assert result["blocked_v0_orchestrator_description_still_present"] is True
    assert result["production_contract_v2_cli_available"] is False
    assert result["preparation_generator_is_in_authorized_implementation_set"] is False


def test_lifecycle_flags_remain_non_authorizing_and_full_graph_is_not_accepted() -> None:
    result = _artifact()["lifecycle_review"]
    assert result["complete_branch_frozen_positive_model_flag"] is True
    assert result["complete_branch_full_graph_independently_validated"] is False
    assert result["post_generation_blocked_branch_frozen_positive_model_flag"] is True
    assert result[
        "post_generation_blocked_branch_full_graph_independently_validated"
    ] is False
    assert result["preflight_blocked_branch_has_no_candidate_artifacts"] is True
    assert result["production_complete_branch_executable"] is False
    assert result["review_accepts_abstract_models_as_execution_authority"] is False


def test_review_is_b_blocked_and_requires_versioned_v3() -> None:
    artifact = _artifact()
    assert artifact["decision"] == (
        "B_BLOCKED_REJECT_STAGE_A_V2_EXECUTION_AUTHORIZATION_REQUIRE_VERSIONED_V3_SUCCESSOR"
    )
    assert artifact["status"].startswith("B_BLOCKED_V2_PREPARATION_PRESERVED")
    assert [row["finding_id"] for row in artifact["blocking_findings"]] == [
        "V2-IR-BLOCK-001-DYNAMIC-CANDIDATE-EDGE-REQUIREDNESS-MISMATCH",
        "V2-IR-BLOCK-002-PREPARATION-GENERATOR-ARTIFACT-DRIFT",
        "V2-IR-BLOCK-003-INVENTORY-ALGORITHM-IMPLEMENTATION-MISMATCH",
        "V2-IR-BLOCK-004-UNDECLARED-PREFIXED-HASH-COMMITMENTS",
    ]
    assert artifact["recommended_next_boundary"]["versioned_successor_target"] == (
        review.SUCCESSOR_TARGET
    )
    assert artifact["authorization"]["versioned_v3_successor_required"] is True


def test_no_stage_a_stage_b_migration_cutover_or_science_is_authorized() -> None:
    artifact = _artifact()
    for key, value in artifact["authorization"].items():
        if key != "versioned_v3_successor_required":
            assert value is False, key
    scope = artifact["review_scope"]
    assert scope["candidate_artifacts_created"] is False
    assert scope["prototype_execution_attempted"] is False
    assert scope["real_stage_a_controls_executed"] == 0
    assert scope["stage_b_executed"] is False
    assert scope["unit_ledger_executed"] is False


def test_authority_registry_and_prototype_state_remain_unchanged() -> None:
    result = _artifact()["authority_and_nonclaim_review"]
    assert result["scientific_target"] == review.SCIENTIFIC_TARGET
    assert result["maintenance_target"] == review.MAINTENANCE_TARGET
    assert result["prototype_path_absent_at_preparation_commit"] is True
    assert result["registry_unchanged_from_source_commit"] is True
    assert result["registry_sha256"] == review.REGISTRY_SHA256


def test_review_output_has_no_self_hash_or_review_commit_binding() -> None:
    artifact = _artifact()
    assert "review_sha256" not in artifact
    assert "review_commit" not in artifact


def test_validation_interpretation_preserves_the_required_narrow_wording() -> None:
    required = (
        "focused preparation, review, authority, registry and exhaustive Lean "
        "validation passed; the combined predecessor invocation timed out, while "
        "its constituent suites subsequently passed independently; the full "
        "unbounded Python aggregate was not run; the repository is not described "
        "as universally green."
    )
    assert _artifact()["validation_interpretation"] == required


def test_review_integration_enrolls_integrity_gate_and_lean_module() -> None:
    relative_test = (
        "formal/python/tests/"
        "test_loop_control_registry_sharding_read_only_prototype_execution_packet_v2_independent_review.py"
    )
    manifest = json.loads(
        (REPO_ROOT / review.GOVERNANCE_MANIFEST_REL).read_text(encoding="utf-8")
    )
    assert manifest["test_tiers"][relative_test] == "TIER_INTEGRITY"
    integrity = manifest["groups"]["integrity_gates"]
    assert integrity["expected_count"] == len(integrity["tests"]) == 70
    assert relative_test in integrity["tests"]
    assert integrity["expected_sha256"] == _sha256(
        "\n".join(integrity["tests"]).encode("utf-8")
    )
    aggregate = (REPO_ROOT / "formal/toe_formal/ToeFormalAll.lean").read_text(
        encoding="utf-8"
    )
    assert (
        "import ToeFormal.Release."
        "LoopControlRegistryShardingReadOnlyPrototypeExecutionPacketV2IndependentReview"
    ) in aggregate
    assert "def trackedModuleCount : Nat := 1067" in aggregate


def test_lean_certificate_binds_blocked_review_and_nonpromotion() -> None:
    lean_path = REPO_ROOT / (
        "formal/toe_formal/ToeFormal/Release/"
        "LoopControlRegistryShardingReadOnlyPrototypeExecutionPacketV2IndependentReview.lean"
    )
    lean = lean_path.read_text(encoding="utf-8")
    review_hash = _sha256(review.OUTPUT_PATH.read_bytes())
    for token in (
        review.PREPARATION_COMMIT,
        review.PACKET_SHA256,
        review.CONTRACT_SHA256,
        review.EDGE_ROOT_SHA256,
        review_hash,
        "def blockingFindingCount : Nat := 4",
        "def unannotatedHashBearingFieldCount : Nat := 10",
        "def inventoryScannerContractConformant : Bool := false",
        "def stageAAuthorized : Bool := false",
        "def versionedV3SuccessorRequired : Bool := true",
        "def stageBAuthorized : Bool := false",
    ):
        assert token in lean


def test_protected_authority_registry_and_implementation_files_are_unchanged() -> None:
    protected = [
        review.REGISTRY_REL,
        review.MAINTENANCE_REL,
        review.AUTHORITY_REL,
        *review.AUTHORIZED_IMPLEMENTATION_PATHS,
    ]
    result = subprocess.run(
        ["git", "diff", review.PREPARATION_COMMIT, "--", *protected],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    assert result.stdout == ""
