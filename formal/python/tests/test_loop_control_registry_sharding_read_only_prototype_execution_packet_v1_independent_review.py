from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess

from formal.python.tools import (
    loop_control_registry_sharding_read_only_prototype_execution_packet_v1_independent_review
    as review,
)


REPO_ROOT = review.REPO_ROOT


def _artifact() -> dict:
    return json.loads(review.OUTPUT_PATH.read_text(encoding="utf-8"))


def _contract() -> dict:
    return json.loads((REPO_ROOT / review.CONTRACT_REL).read_text(encoding="utf-8"))


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def test_blocked_review_regenerates_deterministically() -> None:
    observed = review.OUTPUT_PATH.read_bytes()
    expected = review.canonical_json_bytes(review.build_review())
    assert observed == expected
    assert observed == review.canonical_json_bytes(_artifact())


def test_review_binds_exact_preparation_commit_packet_and_contract() -> None:
    artifact = _artifact()
    assert artifact["reviewed_commit"] == review.REVIEWED_COMMIT
    assert artifact["blocked_v0_baseline_commit"] == review.BLOCKED_V0_BASELINE_COMMIT
    assert artifact["packet_sha256"] == review.PACKET_SHA256
    assert artifact["contract_bundle_sha256"] == review.CONTRACT_SHA256


def test_all_reviewed_git_inputs_match_frozen_identities() -> None:
    observed = review._reviewed_input_evidence()
    assert observed == _artifact()["reviewed_inputs"]
    assert set(observed) == set(review.REVIEWED_INPUTS)


def test_packet_and_contract_are_strict_canonical_finite_json() -> None:
    for relative in (review.PACKET_REL, review.CONTRACT_REL):
        raw = review._git_blob(relative)
        assert not raw.startswith(b"\xef\xbb\xbf")
        assert b"\r" not in raw
        assert raw.endswith(b"\n")
        assert review.canonical_json_bytes(review._strict_json(raw)) == raw


def test_declared_graph_is_acyclic_but_not_byte_faithful() -> None:
    result = review._graph_review(_contract())
    assert result["declared_graph_is_acyclic"] is True
    assert result["actual_direct_content_graph_acyclic"] is True
    assert result["declared_graph_matches_hash_bearing_schema_fields"] is False
    assert result["review_conclusion"] == (
        "B_BLOCKED_DECLARED_HASH_GRAPH_IS_NOT_BYTE_FAITHFUL"
    )
    assert result["declared_outer_graph_node_count"] == 9
    assert result["declared_candidate_graph_node_count"] == 16


def test_source_manifest_edges_have_no_candidate_schema_identity_fields() -> None:
    result = _artifact()["graph_review"]
    assert result["declared_source_manifest_edge_count"] == 15
    assert (
        result[
            "explicit_source_manifest_identity_field_count_in_candidate_and_evidence_schemas"
        ]
        == 0
    )


def test_history_index_crosses_declared_outer_candidate_evidence_phase() -> None:
    result = _artifact()["graph_review"]
    assert result["outer_phase_conflict_reproduced"] is True
    assert (
        result["outer_core_before_evidence_phase_contract_matches_direct_hash_order"]
        is False
    )
    dependencies = result["actual_direct_content_dependencies"]["HISTORY_INDEX"]
    assert dependencies == [
        "CONSUMER_SOURCE_MAP",
        "CUSTODY_MANIFEST",
        "HISTORY_SHARDS",
    ]


def test_runtime_trace_manifest_declared_dependencies_omit_consumer_map() -> None:
    examples = {
        row["node"]: row for row in _artifact()["graph_review"]["mismatch_examples"]
    }
    row = examples["RUNTIME_TRACE_MANIFEST"]
    assert "CONSUMER_SOURCE_MAP" not in row["declared_dependencies"]
    assert "CONSUMER_SOURCE_MAP" in row["observed_direct_content_dependencies"]


def test_consumer_rescan_reproduces_520_current_paths_and_typed_counts() -> None:
    result = review._consumer_review(_contract())
    assert result["baseline_consumer_count"] == 496
    assert result["baseline_runtime_required_count"] == 470
    assert result["baseline_nonruntime_count"] == 26
    assert result["exact_literal_path_count_at_reviewed_commit"] == 517
    assert result["explicit_nonliteral_reader_count"] == 3
    assert result["current_consumer_count_at_reviewed_commit"] == 520
    assert result["current_runtime_required_count_at_reviewed_commit"] == 485
    assert result["current_nonruntime_count_at_reviewed_commit"] == 35
    assert result["added_consumer_count"] == 24
    assert result["removed_consumer_count"] == 0
    assert result["changed_baseline_consumer_count"] == 3
    assert result["current_sorted_path_lf_root_sha256"] == (
        "45a66d4608517dd823ae9b56fea3f54644cc0ae572e7e1160c07ce30593a04a5"
    )


def test_all_four_implementation_paths_are_not_silently_authorized() -> None:
    result = review._implementation_boundary_review(_contract())
    assert result["authorized_implementation_path_count"] == 4
    assert result["authorized_implementation_paths"] == review.AUTHORIZED_IMPLEMENTATION_PATHS
    assert result["fifth_implementation_path_authorized"] is False
    assert result["implementation_bytes_unchanged_from_blocked_v0_baseline"] is True
    assert result["stage_a_implementation_authorized_by_this_review"] is False


def test_one_row_consumer_and_trace_self_rebind_counterexample_is_schema_valid() -> None:
    counterexample = _artifact()["consumer_inventory_and_shadow_contract_review"][
        "candidate_self_rebind_counterexample"
    ]
    assert counterexample["baseline_claimed_consumer_count"] == 496
    assert counterexample["candidate_local_consumer_count"] == 1
    assert counterexample["candidate_local_required_consumer_count"] == 1
    assert counterexample["candidate_local_trace_event_count"] == 1
    assert counterexample["candidate_map_schema_valid"] is True
    assert counterexample["candidate_trace_event_schema_valid"] is True
    assert counterexample["candidate_trace_manifest_schema_valid"] is True
    assert counterexample["cross_document_consumer_or_trace_reconciliation_keys"] == []
    assert counterexample["self_rebound_truncation_rejected_by_reviewed_contract"] is False
    assert counterexample["required_successor_error_code"] == (
        "V1-E-CONSUMER-INVENTORY-CROSS-DOCUMENT"
    )


def test_current_validator_derives_coverage_from_candidate_local_rows() -> None:
    evidence = _artifact()["consumer_inventory_and_shadow_contract_review"][
        "production_validator_evidence_at_reviewed_commit"
    ]
    assert evidence["consumer_trace_validator_start_line"] > 0
    assert evidence["candidate_required_ids_derived_from_candidate_rows_line"] > 0
    assert evidence["execution_preflight_validator_start_line"] > 0
    assert evidence["preflight_to_candidate_consumer_map_reconciliation_present"] is False


def test_control_definitions_reconcile_but_no_stage_a_or_successor_controls_ran() -> None:
    result = review._control_review(_contract())
    assert result["primary_control_count"] == 51
    assert result["readiness_control_count"] == 7
    assert result["inherited_control_count"] == 58
    assert result["runtime_contract_control_count"] == 18
    assert result["control_definition_count"] == 76
    assert result["duplicate_control_id_count"] == 0
    assert result["successor_regression_definition_count"] == 12
    assert result["real_stage_a_controls_executed_by_review"] == 0
    assert result["successor_regression_execution_eligible"] is False
    assert result["successor_regressions_accepted_as_independent_production_mutations"] == 0
    assert result["control_id_root_sha256"] == (
        "d26d65fe981a3bd864e1f7567ef4cd309f9874915fcdf41f5755823779e827eb"
    )
    assert result["control_profile_root_sha256"] == (
        "7168a309bcb668a9c53b64912b0d801bf4c0ee9fd6aaea268e232deee931f1a5"
    )


def test_external_roots_verify_but_consumer_candidate_is_not_cross_bound() -> None:
    result = review._external_root_review(_contract())
    assert result["frozen_input_count"] == 14
    assert result["source_roots_verified"] is True
    assert result["registry_sha256_frozen_outside_candidate"] == review.REGISTRY_SHA256
    assert result["candidate_consumer_inventory_externally_cross_bound"] is False


def test_detached_checkout_regenerates_twice_and_remains_clean() -> None:
    result = review._detached_determinism_review()
    assert result["detached_regeneration_count"] == 2
    assert result["detached_focused_test_count"] == 27
    assert result["packet_and_contract_byte_identical_across_regenerations"] is True
    assert result["generator_check_passed"] is True
    assert result["detached_checkout_clean_after"] is True
    assert result["wall_clock_or_ambient_branch_input_used"] is False


def test_review_is_b_blocked_and_requires_versioned_v2() -> None:
    artifact = _artifact()
    assert artifact["decision"] == (
        "B_BLOCKED_REJECT_ONE_WAY_STAGE_A_V1_EXECUTION_AUTHORIZATION_REQUIRE_VERSIONED_V2_SUCCESSOR"
    )
    assert artifact["status"].startswith("B_BLOCKED_V1_CONTRACT_PRESERVED")
    assert len(artifact["blocking_findings"]) == 3
    assert artifact["recommended_successor"]["required_target"] == review.SUCCESSOR_TARGET
    assert artifact["authorization"]["versioned_v2_successor_required"] is True


def test_no_stage_a_stage_b_migration_cutover_or_science_is_authorized() -> None:
    artifact = _artifact()
    authorization = artifact["authorization"]
    for key, value in authorization.items():
        if key != "versioned_v2_successor_required":
            assert value is False, key
    scope = artifact["review_scope"]
    assert scope["candidate_artifacts_created"] is False
    assert scope["prototype_execution_attempted"] is False
    assert scope["real_stage_a_preterminal_controls_executed"] == 0
    assert scope["stage_b_executed"] is False


def test_authority_registry_and_prototype_state_remain_unchanged() -> None:
    result = _artifact()["authority_and_nonclaim_review"]
    assert result["scientific_target"] == review.SCIENTIFIC_TARGET
    assert result["maintenance_target"] == review.MAINTENANCE_TARGET
    assert result["migration_execution_authorized"] is False
    assert result["stage_b_authorized"] is False
    assert result["prototype_artifacts_created"] is False
    assert result["registry_sha256"] == review.REGISTRY_SHA256


def test_review_output_has_no_self_hash_or_review_commit_binding() -> None:
    artifact = _artifact()
    assert "review_sha256" not in artifact
    assert "review_commit" not in artifact


def test_review_integration_enrolls_one_integrity_gate_and_lean_module() -> None:
    relative_test = (
        "formal/python/tests/"
        "test_loop_control_registry_sharding_read_only_prototype_execution_packet_v1_independent_review.py"
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
        "LoopControlRegistryShardingReadOnlyPrototypeExecutionPacketV1IndependentReview"
    ) in aggregate
    assert "def trackedModuleCount : Nat := 1067" in aggregate


def test_lean_certificate_binds_blocked_review_and_nonpromotion() -> None:
    lean_path = REPO_ROOT / (
        "formal/toe_formal/ToeFormal/Release/"
        "LoopControlRegistryShardingReadOnlyPrototypeExecutionPacketV1IndependentReview.lean"
    )
    lean = lean_path.read_text(encoding="utf-8")
    review_hash = _sha256(review.OUTPUT_PATH.read_bytes())
    for token in (
        review.REVIEWED_COMMIT,
        review.PACKET_SHA256,
        review.CONTRACT_SHA256,
        review.REGISTRY_SHA256,
        review_hash,
        "def blockingFindingCount : Nat := 3",
        "def realStageAControlsExecuted : Nat := 0",
        "def boundedStageAV1AttemptAuthorized : Bool := false",
        "def versionedV2SuccessorRequired : Bool := true",
        "def stageBAuthorized : Bool := false",
    ):
        assert token in lean


def test_protected_files_have_no_worktree_diff() -> None:
    protected = [
        review.REGISTRY_REL,
        review.MAINTENANCE_REL,
        review.AUTHORITY_REL,
        *review.AUTHORIZED_IMPLEMENTATION_PATHS,
    ]
    result = subprocess.run(
        ["git", "diff", "--", *protected],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    assert result.stdout == ""
