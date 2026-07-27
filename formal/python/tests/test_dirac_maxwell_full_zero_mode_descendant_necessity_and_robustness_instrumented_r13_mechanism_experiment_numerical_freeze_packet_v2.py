from __future__ import annotations

import copy
import json
from functools import lru_cache
from pathlib import Path
from typing import Any

import pytest

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_numerical_freeze_packet_v2
    as freeze,
)


ROOT = find_repo_root(Path(__file__))


@lru_cache(maxsize=1)
def _artifact_bytes() -> dict[str, bytes]:
    return freeze.artifact_bytes()


@lru_cache(maxsize=1)
def _artifacts() -> tuple[
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
]:
    raw = _artifact_bytes()
    return tuple(
        json.loads(raw[path].decode("utf-8"))
        for path in (
            freeze.PACKET_RELATIVE_PATH,
            freeze.RUN_MATRIX_RELATIVE_PATH,
            freeze.IDENTITY_RELATIVE_PATH,
            freeze.MANIFEST_RELATIVE_PATH,
            freeze.REPORT_RELATIVE_PATH,
        )
    )  # type: ignore[return-value]


def test_all_five_v2_artifacts_regenerate_exactly_and_deterministically() -> None:
    first = _artifact_bytes()
    assert set(first) == {
        freeze.PACKET_RELATIVE_PATH,
        freeze.RUN_MATRIX_RELATIVE_PATH,
        freeze.IDENTITY_RELATIVE_PATH,
        freeze.MANIFEST_RELATIVE_PATH,
        freeze.REPORT_RELATIVE_PATH,
    }
    assert all((ROOT / path).read_bytes() == raw for path, raw in first.items())
    assert freeze.artifact_bytes() == first


def test_v2_preserves_the_six_physical_and_numerical_inputs() -> None:
    _, matrix, _, _, _ = _artifacts()
    predecessor = json.loads(
        (ROOT / freeze.PREDECESSOR_MATRIX_RELATIVE_PATH).read_text(
            encoding="utf-8"
        )
    )
    assert matrix["record_count"] == predecessor["record_count"] == 6
    assert matrix["expected_run_id_order"] == predecessor["expected_run_id_order"]
    assert matrix["fixed_numerical_settings"] == predecessor["fixed_numerical_settings"]
    for old, new in zip(predecessor["records"], matrix["records"], strict=True):
        assert old["run_id"] == new["run_id"]
        for field in freeze.executor_v2._PHYSICAL_FIELDS:
            assert new[field] == old[field]
    assert matrix["supersedes_blocked_predecessor"][
        "scientific_configuration_changed"
    ] is False


def test_six_scientific_reconstructions_form_three_identical_physical_pairs() -> None:
    _, matrix, _, _, _ = _artifacts()
    closure_hash = matrix["runtime_source_closure_sha256"]
    scientific_hashes: list[str] = []
    physical_hashes: list[str] = []
    records = {record["run_id"]: record for record in matrix["records"]}
    for record in matrix["records"]:
        physical = freeze.executor_v2.build_physical_configuration_core(
            record, closure_hash
        )
        scientific = freeze.executor_v2.build_scientific_input_core(
            record, closure_hash
        )
        physical_hash = freeze.executor_v2.physical_configuration_hash(physical)
        scientific_hash = freeze.executor_v2.scientific_input_hash(scientific)
        assert record["physical_configuration_core"] == physical
        assert record["physical_configuration_core_sha256"] == physical_hash
        assert record["scientific_input_core"] == scientific
        assert record["scientific_input_core_sha256"] == scientific_hash
        assert record["input_hash"] == scientific_hash
        physical_hashes.append(physical_hash)
        scientific_hashes.append(scientific_hash)
    assert len(physical_hashes) == len(scientific_hashes) == 6
    assert len(set(physical_hashes)) == len(set(scientific_hashes)) == 3
    for instrumented_id, control_id in freeze.executor_custody_v2.PAIR_RUN_IDS:
        assert records[instrumented_id]["scientific_input_core_sha256"] == records[
            control_id
        ]["scientific_input_core_sha256"]


def test_all_six_complete_execution_identities_reconstruct_and_are_unique() -> None:
    _, matrix, identity, _, _ = _artifacts()
    closure_hash = matrix["runtime_source_closure_sha256"]
    observed: dict[str, str] = {}
    for record in matrix["records"]:
        run_id = record["run_id"]
        core = freeze.executor_v2.build_complete_execution_identity_core(
            record, closure_hash
        )
        digest = freeze.executor_v2.complete_execution_identity_sha256(
            record, closure_hash
        )
        assert record["complete_execution_identity_core"] == core
        assert record["complete_execution_identity_sha256"] == digest
        assert matrix["complete_execution_identity_contract"][
            "complete_execution_sha256_by_run_id"
        ][run_id] == digest
        assert matrix["full_record_identity_sha256_by_run_id"][run_id] == (
            freeze.executor_v2.full_record_identity_sha256(record)
        )
        observed[run_id] = digest
    assert len(observed) == len(set(observed.values())) == 6
    assert {
        item["run_id"]: item["complete_execution_identity_sha256"]
        for item in identity["outputs"]
    } == observed


def test_all_twenty_mutations_have_the_exact_registered_first_diagnostic() -> None:
    packet, matrix, _, _, _ = _artifacts()
    authority = packet["runtime_execution_authority_proposal"][
        "proposed_review_authority"
    ]
    audit = packet["run_lookup_and_preflight_contract"][
        "identity_mutation_diagnostic_audit"
    ]
    assert audit["mutation_count"] == audit["rejected_count"] == 20
    assert audit["exact_first_diagnostic_count"] == 20
    assert audit["all_passed"] is True
    for field in freeze.executor_v2.IDENTITY_DIAGNOSTIC_FIELDS:
        candidate = copy.deepcopy(matrix)
        candidate["records"][0][field] = copy.deepcopy(
            freeze.semantic_v1.IDENTITY_MUTATION_VALUES[field]
        )
        expected = f"RUN_MATRIX_IDENTITY_FIELD_MISMATCH:{field}"
        assert freeze.executor_v2.strict_validate_matrix(candidate, matrix) == [
            expected
        ]
        assert freeze.executor_v2.strict_validate_matrix(candidate, authority) == [
            expected
        ]


def test_eight_frozen_sources_match_runtime_loaded_paths_bytes_and_loaders() -> None:
    packet, _, _, _, report = _artifacts()
    manifest = packet["source_closure_manifest"]
    closure = manifest["runtime_source_closure"]
    assert manifest["binding_count"] == len(closure["modules"]) == 8
    assert manifest["closure_sha256"] == freeze.sha256_bytes(
        freeze.canonical_json_bytes(closure)
    )
    assert manifest["git_commit_or_blob_identity_decision_bearing"] is False
    for binding in closure["modules"]:
        assert binding["loader_type"] == "SourceFileLoader"
        assert binding["expected_resolved_relative_path"] == binding["relative_path"]
        assert binding["sha256"] == freeze.sha256_bytes(
            (ROOT / binding["relative_path"]).read_bytes()
        )
        assert "source_commit" not in binding
    loaded = packet["preparation_self_validation"][
        "runtime_loaded_source_identity"
    ]
    assert loaded["all_passed"] is True
    assert loaded["loaded_module_count"] == 8
    assert loaded["runtime_source_closure_sha256"] == manifest["closure_sha256"]
    assert all(
        item["path_exact"] and item["bytes_exact"] and item["loader_exact"]
        for item in loaded["loaded_modules"]
    )
    assert report["freeze_summary"]["runtime_source_module_count"] == 8


def test_proposed_authority_is_complete_but_cannot_self_accept() -> None:
    packet, matrix, _, _, _ = _artifacts()
    proposal = packet["runtime_execution_authority_proposal"]
    authority = copy.deepcopy(proposal["proposed_review_authority"])
    assert proposal["fixed_review_anchor_path"] == (
        freeze.executor_custody_v2.REVIEW_ANCHOR_RELATIVE_PATH
    )
    assert authority["execution_authorized"] is False
    assert authority["artifact_bindings"]["freeze_packet"]["sha256"] is None
    assert freeze.executor_v2.strict_validate_matrix(matrix, authority) == []

    accepted = copy.deepcopy(authority)
    accepted["execution_authorized"] = True
    accepted["artifact_bindings"]["freeze_packet"]["sha256"] = (
        freeze.sha256_bytes(_artifact_bytes()[freeze.PACKET_RELATIVE_PATH])
    )
    anchor = {
        "verdict": freeze.executor_custody_v2.EXPECTED_REVIEW_VERDICT,
        freeze.executor_custody_v2.REVIEW_AUTHORITY_FIELD: accepted,
    }
    assert freeze.executor_v2._validate_freeze_anchor(anchor) == []


def test_scientific_contract_and_claim_boundary_remain_unchanged() -> None:
    packet, matrix, identity, manifest, report = _artifacts()
    expected_numerics = {
        "accepted_step_count": 16,
        "checkpoint_count_including_initial": 17,
        "duration": 0.05,
        "grid_size": 16,
        "iteration_cap": 80,
        "time_step": 0.003125,
    }
    assert all(
        matrix["fixed_numerical_settings"][key] == value
        for key, value in expected_numerics.items()
    )
    assert matrix["fixed_numerical_settings"]["tolerances_by_configuration"] == {
        "R10_LOOSE_NEIGHBOR": 1e-8,
        "R13_LOOSE": 1e-8,
        "R13_TIGHT": 1e-12,
    }
    assert packet["equation_block_count"] == 8
    assert packet["mechanism_observable_count"] == 14
    assert packet["classifier_freeze"]["support_constant_count"] == 23
    assert packet["freeze_adversarial_control_count"] == 41
    assert identity["role_payload_file_count"] == 12
    assert report["freeze_summary"]["gamma32_mechanism_decision_count"] == 0
    assert not (ROOT / freeze.EXPERIMENT_OUTPUT_ROOT).exists()
    assert manifest["execution_authorized"] is False
    assert packet["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
    assert packet["selected_next_target"] == freeze.REVIEW_TARGET
    boundary = packet["authority_boundary"]
    assert boundary["numerical_freeze_v2_prepared"] is True
    assert boundary["numerical_freeze_v2_independently_accepted"] is False
    assert boundary["experiment_execution_authorized"] is False
    assert boundary["experiment_execution_performed"] is False
    assert boundary["canonical_robustness"] == "NUMERICALLY_BLOCKED"
    assert boundary["root_mechanism"] == "UNRESOLVED"
    assert boundary["materiality"] == "NOT_EVALUATED_NUMERICAL_BLOCK"


def test_execution_remains_fail_closed_without_an_accepted_v2_review() -> None:
    anchor = ROOT / freeze.executor_custody_v2.REVIEW_ANCHOR_RELATIVE_PATH
    output_root = ROOT / freeze.EXPERIMENT_OUTPUT_ROOT
    if anchor.exists():
        review = json.loads(anchor.read_text(encoding="utf-8"))
        assert review["verdict"] != (
            freeze.executor_custody_v2.EXPECTED_REVIEW_VERDICT
        )
    assert not output_root.exists()
    with pytest.raises(
        freeze.executor_v2.RuntimeCustodyError,
        match="accepted v2 review anchor is absent|REVIEW_ANCHOR_NOT_ACCEPTED",
    ):
        freeze.executor_v2.preflight_frozen_execution(ROOT)
    assert not output_root.exists()
