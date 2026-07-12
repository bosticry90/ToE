from __future__ import annotations

from copy import deepcopy
import hashlib
import json
from pathlib import Path
import re
import subprocess
from typing import Any

from jsonschema import Draft202012Validator
import pytest

from formal.python.tools import (
    loop_control_registry_sharding_read_only_prototype_execution as blocked_v0,
)
from formal.python.tools import (
    loop_control_registry_sharding_read_only_prototype_execution_packet_v1 as successor,
)


PRETERMINAL_STAGE_A_CONTROL_COUNT = 76
SUCCESSOR_REGRESSION_CONTROL_COUNT = 12
RUNTIME_SCHEMA_COUNT = 7

PRODUCTION_LAYOUT_PATHS = [
    "formal/docs/release/loop_control/LOOP_CONTROL_CURRENT_v1.json",
    "formal/docs/release/loop_control/LOOP_CONTROL_HISTORY_INDEX_v1.json",
    "formal/docs/release/loop_control/shards",
    "formal/docs/release/loop_control/LOOP_CONTROL_LEGACY_BYTE_CUSTODY_v1.json.gz",
]
PROTOTYPE_RUN_ROOT = "formal/scratch/loop_control_registry_v1_prototype"

EXPECTED_SCHEMA_NAMES = {
    "execution_source_manifest",
    "runtime_manifest",
    "control_evidence",
    "execution_report",
    "terminal_execution_envelope",
    "preflight_diagnostic",
    "stage_a_independent_review_binding",
}


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _packet() -> dict[str, Any]:
    return _load(successor.PACKET_PATH)


def _contract() -> dict[str, Any]:
    return _load(successor.CONTRACT_PATH)


def _git(*args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        cwd=successor.REPO_ROOT,
        capture_output=True,
        text=True,
        check=check,
    )


def _git_path_exists(commit: str, relative: str) -> bool:
    return (
        _git("cat-file", "-e", f"{commit}:{relative}", check=False).returncode
        == 0
    )


def _walk_schema(value: Any, label: str = "root") -> None:
    if isinstance(value, dict):
        # Conditional ``oneOf`` branches may constrain selected properties
        # without being standalone object schemas.  Closedness applies to each
        # actual object-schema boundary.
        if value.get("type") == "object":
            assert value.get("additionalProperties") is False, label
            assert set(value.get("required", [])) == set(
                value.get("properties", {})
            ), label
        for key, child in value.items():
            _walk_schema(child, f"{label}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            _walk_schema(child, f"{label}[{index}]")


def _valid_complete_control_evidence(schema: dict[str, Any]) -> dict[str, Any]:
    control_ids = schema["properties"]["control_ids"]["const"]
    core_root = "a" * 64
    rows = []
    for row_schema in schema["properties"]["control_results"]["prefixItems"]:
        properties = row_schema["properties"]
        if "validator_profile" in properties:
            expected_errors = properties["expected_error_codes"]["const"]
            row = {
                "baseline_candidate_sha256_after": core_root,
                "baseline_candidate_sha256_before": core_root,
                "baseline_core_candidate_root_sha256": core_root,
                "baseline_recreated_for_control": True,
                "control_family": "INHERITED_STAGE_A",
                "control_id": properties["control_id"]["const"],
                "expected_decision": properties["expected_decision"]["const"],
                "expected_error_codes": expected_errors,
                "observed_decision": properties["expected_decision"]["const"],
                "observed_error_codes": expected_errors,
                "passed": True,
                "positive_baseline_passed_before_mutation": True,
                "subsequent_controls_received_unmodified_baseline": True,
                "validator_profile": properties["validator_profile"]["const"],
            }
        else:
            row = {
                "baseline_core_candidate_root_sha256": core_root,
                "control_family": "RUNTIME_CONTRACT",
                "control_id": properties["control_id"]["const"],
                "expected_error": properties["expected_error"]["const"],
                "fresh_baseline": True,
                "mutation": properties["mutation"]["const"],
                "observed_error": properties["expected_error"]["const"],
                "passed": True,
                "subsequent_controls_unmodified": True,
            }
        assert set(row) == set(row_schema["required"])
        rows.append(row)
    assert [row["control_id"] for row in rows] == control_ids
    return {
        "schema_id": "LOOP_CONTROL_STAGE_A_CONTROL_EVIDENCE_v1",
        "evidence_version": 1,
        "run_id": "stage_a_v1",
        "control_ids": control_ids,
        "control_results": rows,
        "control_result_count": 76,
        "baseline_core_candidate_root_sha256": core_root,
        "primary_control_count": 51,
        "readiness_control_count": 7,
        "runtime_contract_control_count": 18,
        "results_root_algorithm_id": (
            "LOOP_CONTROL_STAGE_A_76_CONTROL_RESULTS_ROOT_v1"
        ),
        "results_root_sha256": "b" * 64,
        "direct_production_control_invocation": {
            "command": successor.DIRECT_TEST_COMMAND,
            "exit_code": 0,
            "stderr_sha256": "c" * 64,
            "stdout_sha256": "d" * 64,
            "test_node_id": successor.DIRECT_TEST_NODE,
        },
        "baseline_isolation_verified": True,
        "all_results_passed": True,
        "block_reason_codes": [],
        "status": "ALL_76_CONTROLS_PASSED",
    }


def _valid_blocked_control_evidence(schema: dict[str, Any]) -> dict[str, Any]:
    blocked = _valid_complete_control_evidence(schema)
    blocked["control_results"][0]["observed_decision"] = "UNEXPECTED"
    blocked["control_results"][0]["observed_error_codes"] = [
        "UNEXPECTED-RUNTIME-ERROR"
    ]
    blocked["control_results"][0]["positive_baseline_passed_before_mutation"] = False
    blocked["control_results"][0]["baseline_recreated_for_control"] = False
    blocked["control_results"][0][
        "subsequent_controls_received_unmodified_baseline"
    ] = False
    blocked["control_results"][0]["passed"] = False
    blocked["direct_production_control_invocation"]["exit_code"] = 1
    blocked["baseline_isolation_verified"] = False
    blocked["all_results_passed"] = False
    blocked["block_reason_codes"] = ["CONTROL-ROW-FAILED"]
    blocked["status"] = "B_BLOCKED"
    return blocked


def _valid_accept_review_binding() -> dict[str, Any]:
    result_rows = [
        {
            "baseline_recreated": True,
            "control_id": control_id,
            "expected_error_code": expected,
            "mutation": mutation,
            "observed_error_code": expected,
            "passed": True,
            "subsequent_controls_unmodified": True,
        }
        for control_id, mutation, expected in successor.SUCCESSOR_NEGATIVE_CONTROLS
    ]
    return {
        "schema_id": "LOOP_CONTROL_STAGE_A_INDEPENDENT_REVIEW_BINDING_v1",
        "execution_commit": "a" * 40,
        "terminal_envelope": {
            "git_blob": "b" * 40,
            "git_commit": "a" * 40,
            "path": (
                "formal/scratch/reviewed/"
                "LOOP_CONTROL_STAGE_A_TERMINAL_EXECUTION_ENVELOPE_v1.json"
            ),
            "sha256": "c" * 64,
            "size_bytes": 1,
        },
        "terminal_envelope_required": True,
        "successor_regression_controls_observed": 12,
        "successor_regression_control_results": result_rows,
        "successor_regression_results_root_sha256": "d" * 64,
        "fresh_baseline_isolation_verified": True,
        "execution_report_status": (
            "STAGE_A_CANDIDATE_COMPLETE_PENDING_TERMINAL_ENVELOPE"
        ),
        "terminal_candidate_status": (
            "STAGE_A_CANDIDATE_COMPLETE_PENDING_INDEPENDENT_REVIEW"
        ),
        "decision": "ACCEPT_STAGE_A_CANDIDATE_ONLY",
        "stage_b_authorized": False,
    }


def test_successor_outputs_are_deterministic_canonical_and_hash_bound() -> None:
    first = successor.build_all()
    second = successor.build_all()
    assert first == second
    assert set(first) == {successor.PACKET_PATH, successor.CONTRACT_PATH}

    for path, expected in first.items():
        assert path.read_bytes() == expected
        assert expected.endswith(b"\n")
        assert b"\r\n" not in expected
        parsed = json.loads(expected)
        assert expected == successor.canonical_json_bytes(parsed)

    packet = _packet()
    contract_raw = successor.CONTRACT_PATH.read_bytes()
    assert packet["contract_bundle"] == {
        "path": successor.CONTRACT_REL,
        "sha256": _sha256(contract_raw),
    }
    assert packet == successor.build_packet()
    assert _contract() == successor.build_contract()


def test_every_source_binding_uses_exact_committed_bytes_oid_and_size() -> None:
    bindings = _contract()["external_trust_contract"][
        "frozen_preparation_inputs"
    ]
    assert set(bindings) == set(successor.EXPECTED_INPUTS)
    for relative, (expected_sha, expected_oid, expected_size) in (
        successor.EXPECTED_INPUTS.items()
    ):
        raw = successor._git_blob(successor.SOURCE_COMMIT, relative)
        assert (_sha256(raw), successor._git_oid(successor.SOURCE_COMMIT, relative), len(raw)) == (
            expected_sha,
            expected_oid,
            expected_size,
        )
        assert bindings[relative] == {
            "git_blob": expected_oid,
            "path": relative,
            "sha256": expected_sha,
            "size_bytes": expected_size,
            "source_commit": successor.SOURCE_COMMIT,
        }


def test_hash_graph_is_the_exact_one_way_topological_chain() -> None:
    graph = _contract()["hash_graph_contract"]
    assert graph["nodes"] == successor.positive_hash_graph()["nodes"]
    assert graph["topological_order"] == successor.GRAPH_ORDER
    assert graph["acyclic"] is True
    assert graph["no_artifact_may_bind_itself"] is True
    assert graph["earlier_artifact_may_bind_later_artifact"] is False
    assert graph["source_manifest_may_bind_runtime_outputs"] is False
    assert graph["terminal_envelope_has_no_outgoing_runtime_hash_dependency"] is True

    ordinal = {
        row["node_id"]: row["ordinal"]
        for row in graph["nodes"]
    }
    assert ordinal == {
        node: index for index, node in enumerate(successor.GRAPH_ORDER)
    }
    for row in graph["nodes"]:
        assert row["binds"] == successor.GRAPH_BINDS[row["node_id"]]
        assert row["node_id"] not in row["binds"]
        assert all(
            ordinal[dependency] < ordinal[row["node_id"]]
            for dependency in row["binds"]
        )

    assert successor.GRAPH_BINDS == {
        "EXTERNAL_TRUST_ROOTS": [],
        "SOURCE_MANIFEST": ["EXTERNAL_TRUST_ROOTS"],
        "CORE_CANDIDATE_ARTIFACTS": ["SOURCE_MANIFEST"],
        "GENERATED_EVIDENCE": [
            "SOURCE_MANIFEST",
            "CORE_CANDIDATE_ARTIFACTS",
        ],
        "RUNTIME_MANIFEST": [
            "SOURCE_MANIFEST",
            "CORE_CANDIDATE_ARTIFACTS",
            "GENERATED_EVIDENCE",
        ],
        "EXECUTION_REPORT": [
            "SOURCE_MANIFEST",
            "CORE_CANDIDATE_ARTIFACTS",
            "GENERATED_EVIDENCE",
            "RUNTIME_MANIFEST",
        ],
        "TERMINAL_ENVELOPE": [
            "SOURCE_MANIFEST",
            "CORE_CANDIDATE_ARTIFACTS",
            "GENERATED_EVIDENCE",
            "RUNTIME_MANIFEST",
            "EXECUTION_REPORT",
        ],
        "POSTTERMINAL_DAG_CONTROL_RESULTS": ["TERMINAL_ENVELOPE"],
        "STAGE_A_INDEPENDENT_REVIEW": [
            "EXTERNAL_TRUST_ROOTS",
            "TERMINAL_ENVELOPE",
            "POSTTERMINAL_DAG_CONTROL_RESULTS",
        ],
    }
    successor.validate_hash_graph(successor.positive_hash_graph())


@pytest.mark.parametrize(
    ("node", "dependency"),
    [
        ("SOURCE_MANIFEST", "SOURCE_MANIFEST"),
        ("RUNTIME_MANIFEST", "TERMINAL_ENVELOPE"),
        ("EXECUTION_REPORT", "STAGE_A_INDEPENDENT_REVIEW"),
    ],
)
def test_hash_graph_validator_rejects_self_loops_and_back_edges(
    node: str, dependency: str
) -> None:
    graph = successor.positive_hash_graph()
    row = next(item for item in graph["nodes"] if item["node_id"] == node)
    row["binds"].append(dependency)
    with pytest.raises(successor.SuccessorPreparationError):
        successor.validate_hash_graph(graph)


def test_generation_order_matches_the_hash_graph_and_has_a_terminal_point() -> None:
    contract = _contract()
    assert contract["generation_order"] == [
        "VERIFY_EXTERNAL_TRUST_ROOTS",
        "WRITE_IMMUTABLE_SOURCE_MANIFEST",
        "GENERATE_AND_FINALIZE_CANDIDATE_ARTIFACTS",
        "WRITE_RUNTIME_MANIFEST",
        "WRITE_STAGE_A_EXECUTION_REPORT",
        "WRITE_TERMINAL_EXECUTION_ENVELOPE",
        "RUN_POSTTERMINAL_DAG_REGRESSION_CONTROLS",
        "INDEPENDENT_REVIEW_BINDS_TERMINAL_ENVELOPE",
    ]
    terminal = contract["terminal_envelope_contract"]
    assert terminal["earlier_artifacts_may_bind_terminal_envelope"] is False
    assert terminal["self_hash_field_allowed"] is False
    assert terminal["stage_a_review_requires_terminal_envelope"] is True
    assert terminal["candidate_coverage_must_equal_runtime_manifest_coverage"] is True


def test_twelve_successor_controls_are_distinct_fresh_and_outside_preterminal_76() -> None:
    contract = _contract()
    control_contract = contract["stage_a_control_contract"]
    results = control_contract["successor_regression_results"]
    expected = successor.SUCCESSOR_NEGATIVE_CONTROLS

    assert control_contract["existing_preterminal_control_count"] == 76
    assert control_contract["existing_preterminal_control_count_changed"] is False
    assert control_contract["successor_regression_control_count"] == 12
    assert control_contract["successor_regressions_are_inside_preterminal_execution_report"] is False
    assert len(results) == len(expected) == SUCCESSOR_REGRESSION_CONTROL_COUNT
    assert [row["control_id"] for row in results] == [row[0] for row in expected]
    assert [row["mutation"] for row in results] == [row[1] for row in expected]
    assert [row["expected_error_code"] for row in results] == [
        row[2] for row in expected
    ]
    assert len({row["control_id"] for row in results}) == 12
    assert len({row["mutation"] for row in results}) == 12
    assert len({row["expected_error_code"] for row in results}) == 12
    assert all(row["passed"] is True for row in results)
    assert all(row["baseline_recreated"] is True for row in results)
    assert all(row["subsequent_controls_unmodified"] is True for row in results)
    assert all(
        row["baseline_sha256_before"] == row["baseline_sha256_after"]
        for row in results
    )
    assert all(
        row["observed_error_code"] == row["expected_error_code"]
        for row in results
    )
    assert results == successor.run_successor_negative_controls()
    assert control_contract["successor_regression_results_root_sha256"] == (
        successor._control_root(results)
    )

    v0 = json.loads(
        successor._git_blob(successor.SOURCE_COMMIT, successor.V0_CONTRACT_REL)
    )
    preterminal_ids = set(
        v0["lifecycle"][
            "stage_a_precutover_execution_after_separate_authorization"
        ]["control_result_order"]
    )
    preterminal_ids.update(
        row["control_id"]
        for row in v0["runtime_validator_contract"]["negative_controls"]
    )
    assert len(preterminal_ids) == PRETERMINAL_STAGE_A_CONTROL_COUNT
    assert preterminal_ids.isdisjoint(row["control_id"] for row in results)


def test_each_successor_mutation_starts_from_an_independent_positive_fixture() -> None:
    pristine = successor.positive_successor_fixture()
    pristine_bytes = successor.compact_json_bytes(pristine)
    assert successor.validate_successor_fixture(pristine) is None
    for _, mutation, expected_error in successor.SUCCESSOR_NEGATIVE_CONTROLS:
        candidate = deepcopy(pristine)
        successor.mutate_fixture(candidate, mutation)
        assert successor.validate_successor_fixture(candidate) == expected_error
        assert successor.compact_json_bytes(pristine) == pristine_bytes


def test_seven_runtime_schemas_are_valid_recursively_closed_and_versioned() -> None:
    schemas = _contract()["runtime_schemas"]
    assert set(schemas) == EXPECTED_SCHEMA_NAMES
    assert len(schemas) == RUNTIME_SCHEMA_COUNT
    for name, schema in schemas.items():
        Draft202012Validator.check_schema(schema)
        _walk_schema(schema, name)
        errors = list(Draft202012Validator(schema).iter_errors({"unknown": True}))
        assert any(error.validator == "additionalProperties" for error in errors), name
        assert schema["$schema"] == "https://json-schema.org/draft/2020-12/schema"
        assert schema["$id"].endswith(f"/{name}.json")


def test_source_runtime_report_terminal_and_review_schema_roles_are_separated() -> None:
    schemas = _contract()["runtime_schemas"]
    source = schemas["execution_source_manifest"]
    source_roles = set(
        source["properties"]["authorized_inputs"]["items"]["properties"]["role"][
            "enum"
        ]
    )
    assert {
        "RUNTIME_MANIFEST",
        "CANDIDATE_ARTIFACT",
        "EXECUTION_REPORT",
        "TERMINAL_ENVELOPE",
        "STAGE_A_INDEPENDENT_REVIEW",
    }.isdisjoint(source_roles)
    assert source["properties"]["runtime_output_count"]["const"] == 0

    runtime = schemas["runtime_manifest"]
    assert "source_manifest" in runtime["required"]
    assert "candidate_artifacts" in runtime["required"]
    assert "evidence_artifacts" in runtime["required"]
    assert "candidate_artifact_root_sha256" in runtime["required"]
    assert "evidence_artifact_root_sha256" in runtime["required"]
    assert runtime["properties"]["expected_control_count"]["const"] == 76
    core_kinds = set(
        runtime["properties"]["candidate_artifacts"]["items"]["properties"][
            "artifact_kind"
        ]["enum"]
    )
    evidence_kinds = set(
        runtime["properties"]["evidence_artifacts"]["items"]["properties"][
            "artifact_kind"
        ]["enum"]
    )
    assert core_kinds == {
        "CURRENT_PROJECTION",
        "HISTORY_INDEX",
        "HISTORY_SHARD",
        "CUSTODY_PAYLOAD",
    }
    assert core_kinds.isdisjoint(evidence_kinds)

    evidence = schemas["control_evidence"]
    assert evidence["properties"]["control_result_count"]["const"] == 76
    assert evidence["properties"]["primary_control_count"]["const"] == 51
    assert evidence["properties"]["readiness_control_count"]["const"] == 7
    assert evidence["properties"]["runtime_contract_control_count"]["const"] == 18
    assert evidence["properties"]["control_ids"]["const"] == (
        _contract()["stage_a_control_contract"]["exact_control_ids"]
    )
    control_rows = evidence["properties"]["control_results"]
    assert control_rows["items"] is False
    assert len(control_rows["prefixItems"]) == 76
    assert [
        row["properties"]["control_id"]["const"]
        for row in control_rows["prefixItems"]
    ] == evidence["properties"]["control_ids"]["const"]
    profiles = _contract()["stage_a_control_contract"]["exact_control_profiles"]
    for row, profile in zip(control_rows["prefixItems"], profiles, strict=True):
        properties = row["properties"]
        assert properties["control_family"]["const"] == profile["control_family"]
        assert properties["control_id"]["const"] == profile["control_id"]
        assert "const" not in properties["passed"]
        if profile["control_family"] == "INHERITED_STAGE_A":
            assert properties["validator_profile"]["const"] == profile["validator_profile"]
            assert properties["expected_decision"]["const"] == profile["expected_decision"]
            assert properties["expected_error_codes"]["const"] == profile["expected_error_codes"]
            assert "const" not in properties["observed_decision"]
            assert "const" not in properties["observed_error_codes"]
            assert "const" not in properties["baseline_recreated_for_control"]
        else:
            assert properties["mutation"]["const"] == profile["mutation"]
            assert properties["expected_error"]["const"] == profile["expected_error"]
            assert "const" not in properties["observed_error"]
            assert "const" not in properties["fresh_baseline"]
            assert "const" not in properties["subsequent_controls_unmodified"]
    assert "baseline_core_candidate_root_sha256" in evidence["required"]
    assert evidence["properties"]["results_root_algorithm_id"]["const"] == (
        "LOOP_CONTROL_STAGE_A_76_CONTROL_RESULTS_ROOT_v1"
    )

    report = schemas["execution_report"]
    assert "runtime_manifest" in report["required"]
    assert "terminal_envelope" not in report["properties"]
    assert report["properties"]["expected_control_count"]["const"] == 76
    assert report["properties"]["control_results_root_algorithm_id"]["const"] == (
        "LOOP_CONTROL_STAGE_A_76_CONTROL_RESULTS_ROOT_v1"
    )

    terminal = schemas["terminal_execution_envelope"]
    assert terminal["properties"]["terminal"]["const"] is True
    assert {
        "source_manifest",
        "runtime_manifest",
        "execution_report",
        "control_evidence",
        "candidate_artifacts",
        "evidence_artifacts",
    } <= set(terminal["required"])
    assert "candidate_artifact_root_sha256" in terminal["required"]
    assert "evidence_artifact_root_sha256" in terminal["required"]
    assert terminal["properties"]["control_results_root_algorithm_id"]["const"] == (
        "LOOP_CONTROL_STAGE_A_76_CONTROL_RESULTS_ROOT_v1"
    )
    assert not any(
        key in terminal["properties"]
        for key in ("self_sha256", "terminal_envelope_sha256")
    )

    review = schemas["stage_a_independent_review_binding"]
    assert review["properties"]["terminal_envelope_required"]["const"] is True
    assert review["properties"]["successor_regression_controls_observed"]["const"] == 12
    assert review["properties"]["stage_b_authorized"]["const"] is False


def test_candidate_internal_hash_graph_is_exact_and_has_only_earlier_phase_edges() -> None:
    candidate = _contract()["candidate_internal_hash_graph"]
    assert candidate["nodes"] == successor.CANDIDATE_INTERNAL_GRAPH
    assert candidate["dependency_semantics"] == (
        "NODE_BINDS_ONLY_EARLIER_PHASE_NODES"
    )
    assert candidate[
        "no_candidate_root_may_be_embedded_IN_ARTIFACTS_USED_TO_COMPUTE_THAT_ROOT"
    ] is True
    assert candidate["projection_may_not_bind_history_index_that_also_binds_projection"] is True
    assert candidate["custody_manifest_may_not_bind_history_index"] is True
    assert candidate["unmodeled_preterminal_artifacts_may_contain_content_identities"] is False

    successor.validate_candidate_internal_graph(deepcopy(candidate["nodes"]))
    for node, row in candidate["nodes"].items():
        assert node not in row["binds"]
        assert all(
            candidate["nodes"][dependency]["phase"] < row["phase"]
            for dependency in row["binds"]
        )

    cycle = deepcopy(candidate["nodes"])
    cycle["CURRENT_PROJECTION"]["binds"].append("RUNTIME_TRACE")
    with pytest.raises(successor.SuccessorPreparationError):
        successor.validate_candidate_internal_graph(cycle)


def test_source_manifest_has_an_exact_unique_role_path_contract() -> None:
    contract = _contract()
    algorithm = contract["source_manifest_validation_algorithm"]
    assert algorithm["authorized_input_count"] == 10
    assert algorithm["exact_role_path_map"] == successor.SOURCE_INPUT_ROLE_PATHS
    assert len(algorithm["exact_role_path_map"]) == 10
    assert len(set(algorithm["exact_role_path_map"].values())) == 10
    assert algorithm["each_role_occurs_exactly_once"] is True
    assert algorithm["implementation_path_count"] == 4
    assert algorithm["implementation_rows_loaded_from_git_not_candidate_values"] is True
    assert algorithm["review_commit_and_blob_required_for_successor_review"] is True
    assert algorithm["source_registry_identity_must_equal_external_frozen_identity"] is True

    source_schema = contract["runtime_schemas"]["execution_source_manifest"]
    row = source_schema["properties"]["authorized_inputs"]["items"]
    assert set(row["properties"]["role"]["enum"]) == set(
        successor.SOURCE_INPUT_ROLE_PATHS
    )
    assert source_schema["properties"]["authorized_inputs"]["minItems"] == 10
    assert source_schema["properties"]["authorized_inputs"]["maxItems"] == 10
    assert {"git_blob", "git_commit", "path", "role", "sha256", "size_bytes"} == set(
        row["required"]
    )


def test_terminal_envelope_freezes_complete_preterminal_inventory_algorithms() -> None:
    contract = _contract()
    algorithms = contract["inventory_algorithms"]
    assert set(algorithms) == {
        "core_candidate_artifact_root",
        "generated_evidence_artifact_root",
        "preterminal_inventory_root",
    }
    candidate = algorithms["core_candidate_artifact_root"]
    assert candidate["row_fields"] == [
        "artifact_kind",
        "path",
        "sha256",
        "size_bytes",
    ]
    assert candidate["row_order"] == "UTF8_PATH_BYTE_ASCENDING"
    assert candidate["row_serializer"] == "COMPACT_CANONICAL_FINITE_JSON_UTF8"
    assert candidate["unique_paths_required"] is True

    evidence = algorithms["generated_evidence_artifact_root"]
    assert evidence["row_fields"] == candidate["row_fields"]
    assert evidence["row_order"] == candidate["row_order"]
    assert evidence["row_serializer"] == candidate["row_serializer"]
    assert evidence["domain"] != candidate["domain"]

    preterminal = algorithms["preterminal_inventory_root"]
    assert preterminal["row_fields"] == [
        "phase",
        "artifact_kind",
        "path",
        "sha256",
        "size_bytes",
    ]
    assert preterminal["exclusions"] == [
        "TERMINAL_ENVELOPE_ITSELF",
        "EXPLICITLY_REMOVED_TRANSIENT_RECONSTRUCTION_BYTES",
    ]
    assert preterminal["unique_paths_required"] is True

    terminal = contract["runtime_schemas"]["terminal_execution_envelope"]
    for field in (
        "preterminal_inventory_algorithm_id",
        "preterminal_artifact_count",
        "preterminal_artifacts",
        "preterminal_inventory_root_sha256",
    ):
        assert field in terminal["required"]
    assert terminal["properties"]["preterminal_inventory_algorithm_id"]["const"] == (
        preterminal["domain"]
    )
    terminal_validation = contract["terminal_validation_algorithm"]
    assert all(value is True for value in terminal_validation.values())


def test_source_root_algorithms_and_runtime_path_kind_map_are_exact() -> None:
    contract = _contract()
    roots = contract["source_manifest_root_algorithms"]
    assert set(roots) == {
        "allowed_output_specification",
        "implementation_tree",
        "input_inventory",
    }
    assert roots["implementation_tree"]["row_fields"] == [
        "path",
        "git_commit",
        "git_blob",
        "sha256",
        "size_bytes",
    ]
    assert roots["implementation_tree"]["row_order"] == (
        "EXACT_AUTHORIZED_FOUR_PATH_ORDER"
    )
    assert roots["input_inventory"]["row_fields"] == [
        "role",
        "path",
        "git_commit",
        "git_blob",
        "sha256",
        "size_bytes",
    ]
    assert roots["input_inventory"]["row_order"] == (
        "UTF8_ROLE_THEN_PATH_BYTE_ASCENDING"
    )
    assert roots["allowed_output_specification"]["preimage"] == (
        "COMPACT_CANONICAL_RUNTIME_PATH_CONTRACT_FROM_REVIEWED_SUCCESSOR_CONTRACT"
    )

    paths = contract["runtime_path_contract"]
    assert paths["path_to_kind_is_closed_and_exact"] is True
    assert set(paths["fixed_paths"].values()) == set(paths["fixed_path_to_kind"])
    assert len(paths["fixed_paths"]) == len(paths["fixed_path_to_kind"]) == 18
    assert paths["fixed_path_to_kind"][paths["fixed_paths"]["control_evidence"]] == (
        "CONTROL_EVIDENCE"
    )
    assert paths["fixed_path_to_kind"][paths["fixed_paths"]["terminal_envelope"]] == (
        "TERMINAL_ENVELOPE"
    )
    assert paths["prototype_runtime_base"] == PROTOTYPE_RUN_ROOT
    assert paths["history_shard_pattern"] == (
        "^history/shards/LOOP_CONTROL_HISTORY_[0-9]{4}[.]jsonl$"
    )
    shard_pattern = re.compile(paths["history_shard_pattern"])
    assert shard_pattern.fullmatch("history/shards/LOOP_CONTROL_HISTORY_0000.jsonl")
    assert shard_pattern.fullmatch("history/shards/LOOP_CONTROL_HISTORY_9999.jsonl")
    assert not shard_pattern.fullmatch("history/shards/LOOP_CONTROL_HISTORY_0000Xjsonl")
    assert not shard_pattern.fullmatch("x/history/shards/LOOP_CONTROL_HISTORY_0000.jsonl")


def test_postterminal_results_are_never_written_or_bound_inside_run_root() -> None:
    storage = _contract()["postterminal_control_storage"]
    assert storage == {
        "allowed_locations": [
            "IN_MEMORY_DURING_INDEPENDENT_REVIEW",
            "INSIDE_EXTERNAL_INDEPENDENT_REVIEW_ARTIFACT",
        ],
        "may_be_written_inside_finalized_run_root": False,
        "terminal_envelope_may_bind_postterminal_results": False,
    }


def test_independent_review_schema_binds_all_twelve_rows_and_their_root() -> None:
    contract = _contract()
    review = contract["runtime_schemas"]["stage_a_independent_review_binding"]
    properties = review["properties"]
    rows = properties["successor_regression_control_results"]
    assert rows["minItems"] == rows["maxItems"] == 12
    assert rows["items"] is False
    assert len(rows["prefixItems"]) == 12
    assert properties["successor_regression_controls_observed"]["const"] == 12
    assert "successor_regression_results_root_sha256" in review["required"]
    assert properties["fresh_baseline_isolation_verified"]["const"] is True
    for row, (control_id, mutation, expected_error) in zip(
        rows["prefixItems"], successor.SUCCESSOR_NEGATIVE_CONTROLS, strict=True
    ):
        props = row["properties"]
        assert props["control_id"]["const"] == control_id
        assert props["mutation"]["const"] == mutation
        assert props["expected_error_code"]["const"] == expected_error
        assert props["observed_error_code"]["const"] == expected_error
        assert props["passed"]["const"] is True
        assert props["baseline_recreated"]["const"] is True
        assert props["subsequent_controls_unmodified"]["const"] is True
    assert contract["stage_a_control_contract"][
        "successor_regression_results_root_sha256"
    ] == successor._control_root(
        contract["stage_a_control_contract"]["successor_regression_results"]
    )

    algorithm = contract["control_evidence_validation_algorithm"]
    assert algorithm["control_ids_equal_exact_frozen_order"] is True
    assert algorithm["control_row_expectations_equal_exact_frozen_v0_profiles"] is True
    assert algorithm["observations_pass_and_isolation_fields_are_runtime_values"] is True
    assert algorithm["every_row_baseline_equals_frozen_core_candidate_root"] is True
    assert algorithm["baseline_before_equals_after_for_every_control"] is True
    assert algorithm["direct_command_and_node_equal_frozen_values"] is True
    assert algorithm["primary_readiness_runtime_partition_equals_51_7_18"] is True
    assert algorithm["blocked_evidence_requires_at_least_one_failed_control_row"] is True


def test_exact_v0_control_profiles_and_canonical_root_are_frozen() -> None:
    contract = _contract()
    control = contract["stage_a_control_contract"]
    profiles = control["exact_control_profiles"]
    independently_extracted = successor._v0_stage_a_control_profiles()
    assert profiles == independently_extracted
    assert control["exact_control_profile_count"] == len(profiles) == 76
    assert [row["ordinal"] for row in profiles] == list(range(76))
    assert [row["control_family"] for row in profiles[:58]] == [
        "INHERITED_STAGE_A"
    ] * 58
    assert [row["control_family"] for row in profiles[58:]] == [
        "RUNTIME_CONTRACT"
    ] * 18
    assert [row["control_id"] for row in profiles] == control["exact_control_ids"]
    v0 = json.loads(
        successor._git_blob(successor.SOURCE_COMMIT, successor.V0_CONTRACT_REL)
    )
    report_schema = v0["runtime_schemas"]["stage_a_precutover_report"]
    source_rows = [
        *report_schema["properties"]["control_results"]["prefixItems"],
        *report_schema["properties"]["runtime_contract_control_results"][
            "prefixItems"
        ],
    ]
    for profile, source_row in zip(profiles, source_rows, strict=True):
        assert "row_schema" not in profile
        assert "row_schema_sha256" not in profile
        properties = source_row["properties"]
        assert profile["control_id"] == properties["control_id"]["const"]
        if profile["control_family"] == "INHERITED_STAGE_A":
            assert profile["validator_profile"] == properties["validator_profile"]["const"]
            assert profile["expected_decision"] == properties["expected_decision"]["const"]
            assert profile["expected_error_codes"] == [
                item["const"]
                for item in properties["expected_error_codes"]["prefixItems"]
            ]
        else:
            assert profile["mutation"] == properties["mutation"]["const"]
            assert profile["expected_error"] == properties["expected_error"]["const"]
        assert profile["source_contract_path"] == successor.V0_CONTRACT_REL
        assert profile["source_contract_sha256"] == (
            successor.EXPECTED_INPUTS[successor.V0_CONTRACT_REL][0]
        )
    algorithm = control["exact_control_profile_root_algorithm"]
    assert algorithm == {
        "domain": "LOOP_CONTROL_STAGE_A_V0_IMMUTABLE_CONTROL_PROFILE_ROOT_v1",
        "row_order": "EXACT_FROZEN_76_CONTROL_PREFIX_ORDER",
        "row_serializer": "COMPACT_CANONICAL_FINITE_JSON_UTF8",
        "root_preimage": "UTF8_DOMAIN_NUL_PLUS_ROWS_JOINED_LF_NO_TERMINAL_LF",
    }
    assert control["exact_control_profile_root_sha256"] == (
        successor._control_profile_root(profiles)
    )


def test_control_result_root_algorithm_and_three_document_equality_are_frozen() -> None:
    contract = _contract()
    root = contract["control_results_root_contract"]
    assert root == {
        "algorithm_id": "LOOP_CONTROL_STAGE_A_76_CONTROL_RESULTS_ROOT_v1",
        "domain": "LOOP_CONTROL_STAGE_A_76_CONTROL_RESULTS_ROOT_v1",
        "row_order": "EXACT_FROZEN_76_CONTROL_PREFIX_ORDER",
        "row_payload": "ENTIRE_CLOSED_CONTROL_RESULT_OBJECT",
        "row_serializer": "COMPACT_CANONICAL_FINITE_JSON_UTF8",
        "root_preimage": "UTF8_DOMAIN_NUL_PLUS_ROWS_JOINED_LF_NO_TERMINAL_LF",
        "control_evidence_execution_report_terminal_roots_must_be_equal": True,
        "all_three_roots_recomputed_from_actual_control_evidence_rows": True,
    }
    schemas = contract["runtime_schemas"]
    assert schemas["control_evidence"]["properties"]["results_root_algorithm_id"][
        "const"
    ] == root["algorithm_id"]
    assert schemas["execution_report"]["properties"][
        "control_results_root_algorithm_id"
    ]["const"] == root["algorithm_id"]
    assert schemas["terminal_execution_envelope"]["properties"][
        "control_results_root_algorithm_id"
    ]["const"] == root["algorithm_id"]
    cross = contract["cross_document_validation_algorithm"]
    assert cross["control_evidence_execution_report_terminal_result_roots_equal"] is True
    assert cross["control_result_root_algorithm_ids_equal_frozen_value"] is True
    evidence = _valid_complete_control_evidence(
        schemas["control_evidence"]
    )
    observed = successor._control_result_root(evidence["control_results"])
    assert re.fullmatch(r"[0-9a-f]{64}", observed)
    changed = deepcopy(evidence["control_results"])
    changed[0]["passed"] = False
    assert successor._control_result_root(changed) != observed


def test_control_evidence_schema_rejects_duplicate_rows_and_nonzero_complete_exit() -> None:
    schema = _contract()["runtime_schemas"]["control_evidence"]
    validator = Draft202012Validator(schema)
    positive = _valid_complete_control_evidence(schema)
    assert validator.is_valid(positive)
    blocked = _valid_blocked_control_evidence(schema)
    assert validator.is_valid(blocked)

    duplicated = deepcopy(positive)
    duplicated["control_results"][1] = deepcopy(duplicated["control_results"][0])
    assert not validator.is_valid(duplicated)

    nonzero_exit = deepcopy(positive)
    nonzero_exit["direct_production_control_invocation"]["exit_code"] = 1
    assert not validator.is_valid(nonzero_exit)

    incomplete_isolation = deepcopy(positive)
    incomplete_isolation["control_results"][0][
        "positive_baseline_passed_before_mutation"
    ] = False
    assert not validator.is_valid(incomplete_isolation)

    invented_codes = deepcopy(positive)
    invented_codes["control_results"][0]["expected_error_codes"] = [
        "INVENTED-BUT-EQUAL"
    ]
    invented_codes["control_results"][0]["observed_error_codes"] = [
        "INVENTED-BUT-EQUAL"
    ]
    assert not validator.is_valid(invented_codes)

    invented_blocked_codes = deepcopy(blocked)
    invented_blocked_codes["control_results"][0]["expected_error_codes"] = [
        "INVENTED-BLOCKED-EXPECTATION"
    ]
    assert not validator.is_valid(invented_blocked_codes)

    invented_runtime_error = deepcopy(positive)
    invented_runtime_error["control_results"][58]["expected_error"] = (
        "INVENTED-BUT-EQUAL"
    )
    invented_runtime_error["control_results"][58]["observed_error"] = (
        "INVENTED-BUT-EQUAL"
    )
    assert not validator.is_valid(invented_runtime_error)

    invented_blocked_runtime_error = deepcopy(blocked)
    invented_blocked_runtime_error["control_results"][58]["expected_error"] = (
        "INVENTED-BLOCKED-EXPECTATION"
    )
    assert not validator.is_valid(invented_blocked_runtime_error)

    blocked_without_failed_row = deepcopy(positive)
    blocked_without_failed_row["all_results_passed"] = False
    blocked_without_failed_row["block_reason_codes"] = ["UNEXPLAINED-BLOCK"]
    blocked_without_failed_row["status"] = "B_BLOCKED"
    assert not validator.is_valid(blocked_without_failed_row)


def test_independent_review_schema_rejects_accept_with_blocked_statuses() -> None:
    schema = _contract()["runtime_schemas"]["stage_a_independent_review_binding"]
    validator = Draft202012Validator(schema)
    positive = _valid_accept_review_binding()
    assert validator.is_valid(positive)

    contradictory = deepcopy(positive)
    contradictory["execution_report_status"] = "B_BLOCKED"
    contradictory["terminal_candidate_status"] = (
        "B_BLOCKED_STAGE_A_CANDIDATE_PRESERVED"
    )
    assert contradictory["decision"] == "ACCEPT_STAGE_A_CANDIDATE_ONLY"
    assert not validator.is_valid(contradictory)


def test_v0_unsatisfiable_preflight_is_preserved_as_history_not_execution_failure() -> None:
    packet = _packet()
    contract = _contract()
    historical = contract["historical_v0_blocked_preflight"]
    assert historical == {
        "candidate_artifacts_created": False,
        "classification": "blocked_preflight_contract_unsatisfiable",
        "controls_executed": 0,
        "controls_expected": 76,
        "error_code": successor.V0_CYCLE_ERROR,
        "implementation_commit": successor.SOURCE_COMMIT,
        "prototype_run_root_created": False,
        "source_registry_sha256": successor.SOURCE_REGISTRY_SHA256,
        "stage_b_authorized": False,
        "v0_contract": contract["external_trust_contract"]["frozen_preparation_inputs"][successor.V0_CONTRACT_REL],
        "v0_independent_review": contract["external_trust_contract"]["frozen_preparation_inputs"][successor.V0_REVIEW_REL],
    }
    assert packet["v0_blocked_preflight"] == {
        "classification": "blocked_preflight_contract_unsatisfiable",
        "error_code": successor.V0_CYCLE_ERROR,
        "implementation_commit": successor.SOURCE_COMMIT,
        "source_registry_sha256": successor.SOURCE_REGISTRY_SHA256,
    }

    observed = blocked_v0.contract_preflight()
    assert observed["block_code"] == "STAGE_A-BLOCKED-ARTIFACT-HASH-CYCLE"
    assert observed["controls_expected"] == 76
    assert observed["controls_observed"] == 0
    assert observed["run_root_created"] is False
    assert observed["prototype_artifacts_created"] is False
    assert observed["source_registry_modified"] is False
    assert observed["stage_b_behavior"] is False


def test_exact_four_path_implementation_commit_is_preserved_and_bound() -> None:
    contract = _contract()
    implementation = contract["implementation_path_contract"]
    assert implementation["authorized_path_count"] == 4
    assert implementation["authorized_paths"] == successor.AUTHORIZED_IMPLEMENTATION_PATHS
    assert set(implementation["baseline_at_blocked_v0_commit"]) == set(
        successor.AUTHORIZED_IMPLEMENTATION_PATHS
    )
    assert implementation["v0_blocked_implementation_commit_must_not_be_amended"] is True

    changed = _git(
        "diff-tree",
        "--no-commit-id",
        "--name-only",
        "-r",
        successor.SOURCE_COMMIT,
    ).stdout.splitlines()
    assert changed == sorted(successor.AUTHORIZED_IMPLEMENTATION_PATHS)
    for relative in successor.AUTHORIZED_IMPLEMENTATION_PATHS:
        assert _git_path_exists(successor.SOURCE_COMMIT, relative)
        assert (successor.REPO_ROOT / relative).is_file()


def test_source_commit_has_implementation_but_no_production_or_prototype_layout() -> None:
    layout = _contract()["source_commit_layout"]
    assert layout["implementation_paths_present"] == {
        path: True for path in successor.AUTHORIZED_IMPLEMENTATION_PATHS
    }
    assert layout["production_and_prototype_paths_absent"] == {
        path: True for path in successor.PRODUCTION_LAYOUT_PATHS
    }
    for relative in PRODUCTION_LAYOUT_PATHS + [PROTOTYPE_RUN_ROOT]:
        assert not _git_path_exists(successor.SOURCE_COMMIT, relative), relative
    for relative in PRODUCTION_LAYOUT_PATHS:
        assert not (successor.REPO_ROOT / relative).exists(), relative
    assert not (successor.REPO_ROOT / PROTOTYPE_RUN_ROOT).exists()


def test_packet_is_preparation_only_and_preserves_all_authority() -> None:
    packet = _packet()
    contract = _contract()
    assert packet["scientific_target"] == successor.SCIENTIFIC_TARGET
    assert packet["maintenance_target"] == successor.MAINTENANCE_TARGET
    assert packet["counts"] == {
        "authorized_implementation_path_count": 4,
        "existing_stage_a_control_count": 76,
        "runtime_schema_count": 7,
        "successor_regression_control_count": 12,
    }
    assert packet["authorization"]["independent_review_required"] is True
    assert all(
        value is False
        for key, value in packet["authorization"].items()
        if key != "independent_review_required"
    )
    assert packet["boundary"]["one_way_contract_prepared_only"] is True
    assert all(
        value is False
        for key, value in packet["boundary"].items()
        if key != "one_way_contract_prepared_only"
    )
    assert contract["authorization"]["packet_independent_review_required"] is True
    assert all(
        value is False
        for key, value in contract["authorization"].items()
        if key != "packet_independent_review_required"
    )
    assert contract["nonpromotion"] == {
        "consumer_cutover_performed": False,
        "current_projection_authoritative": False,
        "maintenance_target": successor.MAINTENANCE_TARGET,
        "monolith_remains_authoritative_and_unchanged": True,
        "pillar_or_seam_claim_changed": False,
        "prototype_artifacts_created": False,
        "scientific_target": successor.SCIENTIFIC_TARGET,
        "stage_a_execution_performed": False,
        "stage_b_authorized": False,
        "unit_ledger_executed": False,
    }

    maintenance = json.loads(
        successor._git_blob(
            successor.SOURCE_COMMIT, successor.MAINTENANCE_AUTHORITY_REL
        )
    )
    assert maintenance["current_maintenance_target"] == successor.MAINTENANCE_TARGET
    assert maintenance["scientific_authority"]["current_target"] == successor.SCIENTIFIC_TARGET
    assert maintenance["boundary"]["migration_execution_authorized"] is False

    protected = [
        successor.REGISTRY_REL,
        successor.MAINTENANCE_AUTHORITY_REL,
        successor.AUTHORITATIVE_SURFACES_REL,
    ]
    assert _git(
        "diff", "--name-only", successor.SOURCE_COMMIT, "--", *protected
    ).stdout.strip() == ""


def test_failure_semantics_preserve_fail_closed_stage_boundaries() -> None:
    failure = _contract()["failure_semantics"]
    assert failure == {
        "post_finalization_control_failure": (
            "PRESERVE_B_BLOCKED_CANDIDATE_SET_AND_TERMINAL_ENVELOPE"
        ),
        "pre_finalization_generation_failure": (
            "PRESERVE_PARTIAL_WORKSPACE_AND_BOUNDED_DIAGNOSTIC_"
            "NO_CANONICAL_TERMINAL_CLAIM"
        ),
        "preflight_contract_failure": (
            "EMIT_ONLY_BOUNDED_DIAGNOSTIC_NO_CANONICAL_PROTOTYPE_CANDIDATE_SET"
        ),
        "review_mismatch": (
            "PRESERVE_EXECUTION_SET_AND_EMIT_BLOCKED_INDEPENDENT_REVIEW"
        ),
        "source_registry_may_change_on_failure": False,
    }


def test_preparation_integration_is_complete_without_implementation_or_authority_edits() -> None:
    relative_test = (
        "formal/python/tests/"
        "test_loop_control_registry_sharding_read_only_prototype_execution_packet_v1.py"
    )
    manifest = _load(
        successor.REPO_ROOT / "formal/docs/release/GOVERNANCE_TEST_MANIFEST_v1.json"
    )
    assert manifest["test_tiers"][relative_test] == "TIER_INTEGRITY"
    integrity = manifest["groups"]["integrity_gates"]
    assert relative_test in integrity["tests"]
    assert integrity["expected_count"] == len(integrity["tests"]) == 67
    assert integrity["expected_sha256"] == _sha256(
        "\n".join(integrity["tests"]).encode("utf-8")
    )

    lean_relative = (
        "formal/toe_formal/ToeFormal/Release/"
        "LoopControlRegistryShardingReadOnlyPrototypeExecutionPacketV1.lean"
    )
    expected_lf_paths = [
        successor.PACKET_REL,
        successor.CONTRACT_REL,
        "formal/python/tools/loop_control_registry_sharding_read_only_prototype_execution_packet_v1.py",
        relative_test,
        lean_relative,
    ]
    attributes = (successor.REPO_ROOT / ".gitattributes").read_text(encoding="utf-8")
    for relative in expected_lf_paths:
        assert f"{relative} text eol=lf" in attributes

    command = (
        "formal.python.tools."
        "loop_control_registry_sharding_read_only_prototype_execution_packet_v1 --check"
    )
    assert command in (successor.REPO_ROOT / "README.md").read_text(encoding="utf-8")
    assert command in (successor.REPO_ROOT / "DEVELOPMENT.md").read_text(encoding="utf-8")

    lean = (successor.REPO_ROOT / lean_relative).read_text(encoding="utf-8")
    for token in (
        _sha256(successor.PACKET_PATH.read_bytes()),
        _sha256(successor.CONTRACT_PATH.read_bytes()),
        successor.V0_CYCLE_ERROR,
        "def existingStageAControlCount : Nat := 76",
        "def successorRegressionControlCount : Nat := 12",
        "def runtimeSchemaCount : Nat := 7",
        "def prototypeExecutionAuthorized : Bool := false",
        "def stageBAuthorized : Bool := false",
        "def scientificTargetRotated : Bool := false",
        "def maintenanceTargetRotated : Bool := false",
    ):
        assert token in lean

    aggregate = (
        successor.REPO_ROOT / "formal/toe_formal/ToeFormalAll.lean"
    ).read_text(encoding="utf-8")
    assert (
        "import ToeFormal.Release."
        "LoopControlRegistryShardingReadOnlyPrototypeExecutionPacketV1"
    ) in aggregate
    assert "def trackedModuleCount : Nat := 1064" in aggregate
