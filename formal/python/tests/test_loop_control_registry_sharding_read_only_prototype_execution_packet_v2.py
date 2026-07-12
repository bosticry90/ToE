from __future__ import annotations

import base64
from copy import deepcopy
import gzip
import json
from pathlib import Path
import re
import subprocess
from typing import Any, Iterable, Mapping, Sequence

from jsonschema import Draft202012Validator
import pytest

from formal.python.tools import (
    loop_control_registry_sharding_read_only_prototype_execution_packet_v2 as v2,
)


AUTHORITATIVE_SOURCE_COMMIT = "81a3555a1f83a37ec01bacc247f45d1a5bfe8430"

EXPECTED_EDGE_ROW_KEYS = {
    "blocked_path_applicability",
    "complete_path_applicability",
    "containing_artifact_type",
    "containing_generation_ordinal",
    "containing_generation_phase",
    "containing_schema_id",
    "hash_semantics",
    "referenced_artifact_type",
    "referenced_generation_ordinal",
    "referenced_generation_phase",
    "required_optional_status",
    "schema_field_path",
    "target_resolver",
}

EXPECTED_RECONCILIATION_KEYS = {
    "baseline_changed_paths_require_changed_delta_rows",
    "candidate_identity_set_equals_fresh_preflight_identity_set",
    "candidate_local_expected_count_forbidden",
    "candidate_runtime_required_set_equals_fresh_derived_preflight_set",
    "duplicate_consumer_ids_rejected",
    "fresh_consumers_may_not_be_omitted",
    "independent_review_rescans_instead_of_trusting_execution_inventory",
    "invented_consumers_rejected",
    "nonruntime_rows_remain_present_and_typed",
    "preflight_inventory_mutation_after_source_manifest_rejected",
    "runtime_trace_consumer_ids_must_be_known_runtime_required_ids",
    "runtime_trace_identity_set_equals_runtime_required_identity_set",
}

EXPECTED_LEGACY_DAG_CONTROLS = [
    (
        "DAG-V1-NC-001",
        "source_manifest_inventories_runtime_manifest",
        "V1-E-UNSATISFIABLE-ARTIFACT-MANIFEST-CYCLE",
    ),
    (
        "DAG-V1-NC-002",
        "runtime_manifest_omits_source_manifest_binding",
        "V1-E-RUNTIME-SOURCE-MANIFEST-BINDING-MISSING",
    ),
    (
        "DAG-V1-NC-003",
        "runtime_manifest_binds_modified_source_manifest",
        "V1-E-RUNTIME-SOURCE-MANIFEST-BINDING-MISMATCH",
    ),
    (
        "DAG-V1-NC-004",
        "terminal_envelope_included_in_earlier_manifest",
        "V1-E-HASH-DAG-FORWARD-REFERENCE",
    ),
    (
        "DAG-V1-NC-005",
        "terminal_envelope_hashes_itself",
        "V1-E-TERMINAL-ENVELOPE-SELF-REFERENCE",
    ),
    (
        "DAG-V1-NC-006",
        "execution_report_and_terminal_bind_reciprocally",
        "V1-E-EXECUTION-TERMINAL-CYCLE",
    ),
    (
        "DAG-V1-NC-007",
        "candidate_rebinds_external_expected_source_hash",
        "V1-E-EXTERNAL-TRUST-ROOT-REBIND",
    ),
    (
        "DAG-V1-NC-008",
        "runtime_manifest_precedes_candidate_finalization",
        "V1-E-RUNTIME-MANIFEST-INCOMPLETE-CANDIDATE-SET",
    ),
    (
        "DAG-V1-NC-009",
        "source_manifest_contains_temporary_or_wall_clock_field",
        "V1-E-SOURCE-MANIFEST-NONDETERMINISTIC-FIELD",
    ),
    (
        "DAG-V1-NC-010",
        "review_accepts_chain_without_terminal_envelope",
        "V1-E-REVIEW-MISSING-TERMINAL-ENVELOPE",
    ),
    (
        "DAG-V1-NC-011",
        "terminal_envelope_omits_candidate_shard",
        "V1-E-TERMINAL-CANDIDATE-COVERAGE",
    ),
    (
        "DAG-V1-NC-012",
        "terminal_envelope_binds_execution_report_from_other_run",
        "V1-E-TERMINAL-CROSS-RUN-BINDING",
    ),
]

EXPECTED_V2_NEGATIVE_CONTROLS = [
    (
        "V2-NC-001",
        "declared_graph_differs_from_schema_graph",
        "V2-E-DECLARED-SCHEMA-GRAPH-MISMATCH",
    ),
    (
        "V2-NC-002",
        "schema_graph_differs_from_generation_order",
        "V2-E-SCHEMA-GENERATION-ORDER-MISMATCH",
    ),
    (
        "V2-NC-003",
        "undeclared_hash_bearing_field",
        "V2-E-HASH-FIELD-UNDECLARED",
    ),
    (
        "V2-NC-004",
        "later_phase_artifact_required_too_early",
        "V2-E-LATER-PHASE-REFERENCE",
    ),
    (
        "V2-NC-005",
        "consumer_map_truncated_to_one_row",
        "V2-E-CONSUMER-INVENTORY-INCOMPLETE",
    ),
    (
        "V2-NC-006",
        "trace_truncated_to_match_consumer_map",
        "V2-E-RUNTIME-TRACE-INCOMPLETE",
    ),
    (
        "V2-NC-007",
        "consumer_map_and_trace_locally_rebound",
        "V2-E-CONSUMER-LOCAL-REBIND",
    ),
    (
        "V2-NC-008",
        "stale_historical_count_treated_as_current_truth",
        "V2-E-STALE-CONSUMER-COUNT",
    ),
    (
        "V2-NC-009",
        "fresh_consumer_omitted",
        "V2-E-FRESH-CONSUMER-OMITTED",
    ),
    (
        "V2-NC-010",
        "invented_consumer_inserted",
        "V2-E-CONSUMER-INVENTED",
    ),
    (
        "V2-NC-011",
        "runtime_required_consumer_classified_nonruntime",
        "V2-E-RUNTIME-REQUIRED-MISCLASSIFIED",
    ),
    (
        "V2-NC-012",
        "baseline_path_changed_without_delta_classification",
        "V2-E-BASELINE-CHANGE-UNCLASSIFIED",
    ),
    (
        "V2-NC-013",
        "preflight_inventory_altered_after_source_manifest_creation",
        "V2-E-PREFLIGHT-INVENTORY-BINDING-MISMATCH",
    ),
    (
        "V2-NC-014",
        "consumer_inventory_derived_from_candidate",
        "V2-E-CONSUMER-INVENTORY-TRUST-ROOT",
    ),
    (
        "V2-NC-015",
        "review_trusts_execution_inventory_without_rescan",
        "V2-E-REVIEW-CONSUMER-RESCAN-REQUIRED",
    ),
]


def _git(*args: str, check: bool = True) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        ["git", *args],
        cwd=v2.REPO_ROOT,
        capture_output=True,
        check=check,
    )


def _git_blob(commit: str, relative: str) -> bytes:
    result = _git("show", f"{commit}:{relative}", check=False)
    assert result.returncode == 0, f"missing committed input: {commit}:{relative}"
    return result.stdout


def _git_oid(commit: str, relative: str) -> str:
    return _git("rev-parse", f"{commit}:{relative}").stdout.decode("ascii").strip()


def _load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _normalise_controls(rows: Iterable[Any]) -> list[tuple[str, str, str]]:
    output: list[tuple[str, str, str]] = []
    for row in rows:
        if isinstance(row, Mapping):
            output.append(
                (
                    str(row["control_id"]),
                    str(row["mutation"]),
                    str(row["expected_error_code"]),
                )
            )
        else:
            control_id, mutation, error_code = row
            output.append((str(control_id), str(mutation), str(error_code)))
    return output


def _walk(
    value: Any, path: tuple[str, ...] = ()
) -> Iterable[tuple[tuple[str, ...], Any]]:
    yield path, value
    if isinstance(value, Mapping):
        for key, child in value.items():
            yield from _walk(child, (*path, str(key)))
    elif isinstance(value, Sequence) and not isinstance(
        value, (str, bytes, bytearray)
    ):
        for index, child in enumerate(value):
            yield from _walk(child, (*path, str(index)))


def _schema_for_edge(
    schemas: Mapping[str, dict[str, Any]], edge: Mapping[str, Any]
) -> dict[str, Any]:
    matching = [
        schema
        for schema in schemas.values()
        if schema["$id"] == edge["containing_schema_id"]
    ]
    assert len(matching) == 1
    return matching[0]


def _schema_field(schema: dict[str, Any], pointer: str) -> dict[str, Any]:
    node: dict[str, Any] = schema
    for token in pointer.strip("/").split("/"):
        assert token != "*", "negative-control helper requires a non-array field"
        decoded = token.replace("~1", "/").replace("~0", "~")
        node = node["properties"][decoded]
    return node


def _compact_json_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")


def _artifact_identity(path: str, raw: bytes) -> dict[str, Any]:
    return {
        "path": path,
        "sha256": v2.sha256(raw),
        "size_bytes": len(raw),
    }


def _encoded_document_bytes(
    artifact_type: str, document: dict[str, Any]
) -> bytes:
    if artifact_type == "HISTORY_SHARD":
        return _compact_json_bytes(document) + b"\n"
    return v2.canonical_json_bytes(document)


def _rebind_trace_and_terminal_chain(fixture: dict[str, Any]) -> None:
    fixture["artifact_bytes"]["RUNTIME_TRACE"] = b"".join(
        _compact_json_bytes(event) + b"\n"
        for event in fixture["trace_documents"]
    )
    trace_manifest = fixture["documents"]["RUNTIME_TRACE_MANIFEST"]
    trace_manifest["runtime_trace"] = _artifact_identity(
        trace_manifest["runtime_trace"]["path"],
        fixture["artifact_bytes"]["RUNTIME_TRACE"],
    )
    fixture["artifact_bytes"]["RUNTIME_TRACE_MANIFEST"] = (
        v2.canonical_json_bytes(trace_manifest)
    )
    v2._rebind_runtime_and_later(fixture)


def _independent_hash_fields(
    schema: Mapping[str, Any], path: str = ""
) -> set[tuple[str, str]]:
    """Enumerate SHA-256 leaves without using the generator's walker."""

    output: set[tuple[str, str]] = set()
    properties = schema.get("properties")
    if isinstance(properties, Mapping):
        for name, child in properties.items():
            token = str(name).replace("~", "~0").replace("/", "~1")
            child_path = f"{path}/{token}"
            if isinstance(child, Mapping) and (
                name == "sha256" or str(name).endswith("_sha256")
            ):
                annotation = child.get("x-toe-hash-edge")
                assert isinstance(annotation, Mapping), child_path
                output.add(
                    (child_path, str(annotation["referenced_artifact_type"]))
                )
            if isinstance(child, Mapping):
                output |= _independent_hash_fields(child, child_path)
    items = schema.get("items")
    if isinstance(items, Mapping):
        output |= _independent_hash_fields(items, f"{path}/*")
    prefix_items = schema.get("prefixItems")
    if isinstance(prefix_items, Sequence):
        for child in prefix_items:
            if isinstance(child, Mapping):
                output |= _independent_hash_fields(child, f"{path}/*")
    for keyword in ("oneOf", "allOf", "anyOf"):
        alternatives = schema.get(keyword)
        if isinstance(alternatives, Sequence):
            for child in alternatives:
                if isinstance(child, Mapping):
                    output |= _independent_hash_fields(child, path)
    return output


def test_v2_outputs_are_deterministic_canonical_and_hash_bound() -> None:
    first = v2.build_all()
    second = v2.build_all()
    assert first == second
    assert set(first) == {v2.CONTRACT_PATH, v2.PACKET_PATH}

    for path, expected in first.items():
        assert path.read_bytes() == expected
        assert expected.endswith(b"\n")
        assert not expected.startswith(b"\xef\xbb\xbf")
        assert b"\r" not in expected
        assert expected == v2.canonical_json_bytes(json.loads(expected))

    contract_raw = v2.CONTRACT_PATH.read_bytes()
    assert _load(v2.CONTRACT_PATH) == v2.build_contract()
    assert _load(v2.PACKET_PATH) == v2.build_packet(contract_raw)
    assert v2.build_packet(contract_raw)["contract_bundle"] == {
        "path": v2.CONTRACT_REL,
        "sha256": v2.sha256(contract_raw),
    }


def test_frozen_external_roots_use_exact_committed_bytes_oid_and_size() -> None:
    assert v2.SOURCE_COMMIT == AUTHORITATIVE_SOURCE_COMMIT
    bindings = v2.build_contract()["external_roots_of_trust"][
        "frozen_preparation_inputs"
    ]
    assert set(bindings) == set(v2.EXPECTED_INPUTS)

    for relative, (expected_sha, expected_oid, expected_size) in (
        v2.EXPECTED_INPUTS.items()
    ):
        raw = _git_blob(v2.SOURCE_COMMIT, relative)
        observed = {
            "git_blob": _git_oid(v2.SOURCE_COMMIT, relative),
            "path": relative,
            "sha256": v2.sha256(raw),
            "size_bytes": len(raw),
            "source_commit": v2.SOURCE_COMMIT,
        }
        assert observed == {
            "git_blob": expected_oid,
            "path": relative,
            "sha256": expected_sha,
            "size_bytes": expected_size,
            "source_commit": v2.SOURCE_COMMIT,
        }
        assert bindings[relative] == observed


def test_runtime_schemas_mechanically_derive_the_exact_reviewed_edge_table() -> None:
    schemas = v2.build_runtime_schemas()
    assert schemas == v2.build_artifact_schemas()
    assert len(schemas) == v2.RUNTIME_SCHEMA_COUNT
    assert v2.RUNTIME_SCHEMA_COUNT >= 8
    schema_ids = []
    for name, schema in schemas.items():
        Draft202012Validator.check_schema(schema)
        assert schema["$id"].startswith("https://toe.local/schema/")
        assert schema["$id"].endswith(".json")
        schema_ids.append(schema["$id"])
    assert len(schema_ids) == len(set(schema_ids))

    edges = v2.derive_reviewed_edge_table(schemas)
    assert edges == v2.derive_schema_edges(schemas)
    assert edges == v2.REVIEWED_EDGE_TABLE
    assert edges
    assert all(set(row) == EXPECTED_EDGE_ROW_KEYS for row in edges)
    assert len(edges) == len(
        {
            (
                row["containing_artifact_type"],
                row["schema_field_path"],
                row["referenced_artifact_type"],
            )
            for row in edges
        }
    )
    assert all(
        row["referenced_generation_ordinal"]
        < row["containing_generation_ordinal"]
        for row in edges
    )

    order = v2.validate_schema_derived_graph(schemas, deepcopy(edges))
    contract = v2.build_contract()
    reviewed = contract["reviewed_schema_hash_edge_table"]
    assert reviewed["rows"] == edges
    assert reviewed["edge_count"] == len(edges)
    assert set(reviewed["edge_row_keys"]) == EXPECTED_EDGE_ROW_KEYS
    assert contract["schema_derived_graph_validation"][
        "derived_topological_order"
    ] == order
    independent = set()
    runtime_member_types = schemas["runtime_manifest"]["properties"][
        "candidate_artifacts"
    ]["items"]["properties"]["artifact_type"]["enum"]
    for name, schema in schemas.items():
        artifact_type = v2._schema_artifact_type(name)
        if artifact_type == "PREFLIGHT_DIAGNOSTIC":
            continue
        for field_path, target in _independent_hash_fields(schema):
            targets = (
                runtime_member_types
                if target == "DYNAMIC_CANDIDATE_ARTIFACT"
                else [target]
            )
            independent.update(
                (artifact_type, field_path, resolved_target)
                for resolved_target in targets
            )
    assert independent == {
        (
            row["containing_artifact_type"],
            row["schema_field_path"],
            row["referenced_artifact_type"],
        )
        for row in edges
    }


def test_dynamic_candidate_hash_edge_declares_its_sibling_target_resolution() -> None:
    schemas = v2.build_runtime_schemas()
    edges = v2.derive_reviewed_edge_table(schemas)
    dynamic = [
        row
        for row in edges
        if row["containing_artifact_type"] == "RUNTIME_MANIFEST"
        and row["schema_field_path"] == "/candidate_artifacts/*/sha256"
    ]
    member_types = schemas["runtime_manifest"]["properties"][
        "candidate_artifacts"
    ]["items"]["properties"]["artifact_type"]["enum"]
    assert {row["referenced_artifact_type"] for row in dynamic} == set(
        member_types
    )
    assert all(
        row["target_resolver"]
        == f"SIBLING_ARTIFACT_TYPE={row['referenced_artifact_type']}"
        and row["referenced_generation_ordinal"]
        == v2.ARTIFACT_PHASES[row["referenced_artifact_type"]][1]
        for row in dynamic
    )
    assert v2.validate_schema_derived_graph(schemas, edges)

    schemas["runtime_manifest"]["properties"]["candidate_artifacts"][
        "items"
    ]["properties"]["artifact_type"]["enum"].append("TERMINAL_ENVELOPE")
    with pytest.raises(
        v2.V2PreparationError, match="^V2-E-LATER-PHASE-REFERENCE$"
    ):
        v2.validate_schema_derived_graph(
            schemas, v2.derive_reviewed_edge_table(schemas)
        )

    sha_schema = schemas["runtime_manifest"]["properties"][
        "candidate_artifacts"
    ]["items"]["properties"]["sha256"]
    assert sha_schema["x-toe-hash-edge"] == {
        "hash_semantics": "MEMBER_CONTENT_SHA256",
        "referenced_artifact_type": "DYNAMIC_CANDIDATE_ARTIFACT",
        "target_resolver": "SIBLING_ARTIFACT_TYPE",
    }


def test_const_only_hash_field_is_present_in_the_reviewed_edge_table() -> None:
    rows = [
        row
        for row in v2.REVIEWED_EDGE_TABLE
        if row["containing_artifact_type"] == "VALIDATION_REPORT"
        and row["schema_field_path"] == "/profile_control_root_sha256"
    ]
    assert len(rows) == 1
    assert rows[0]["referenced_artifact_type"] == "CONTROL_PROFILE"
    assert rows[0]["hash_semantics"] == "ORDERED_CONTROL_PROFILE_ROOT"

    variants = v2.build_runtime_schemas()["validation_report"]["oneOf"]
    assert {
        variant["properties"]["profile_control_root_sha256"]["const"]
        for variant in variants
    }
    assert all(
        variant["properties"]["profile_control_root_sha256"][
            "x-toe-hash-edge"
        ]["referenced_artifact_type"]
        == "CONTROL_PROFILE"
        for variant in variants
    )


def test_undeclared_hash_field_and_declared_schema_disagreement_fail_closed() -> None:
    schemas = v2.build_runtime_schemas()
    schemas["execution_source_manifest"]["properties"][
        "rogue_optional_sha256"
    ] = {"pattern": "^[0-9a-f]{64}$", "type": "string"}
    with pytest.raises(
        v2.V2PreparationError, match=r"^V2-E-HASH-FIELD-UNDECLARED:"
    ):
        v2.derive_reviewed_edge_table(schemas)

    schemas = v2.build_runtime_schemas()
    edges = v2.derive_reviewed_edge_table(schemas)
    declared = deepcopy(edges)
    declared.pop()
    with pytest.raises(
        v2.V2PreparationError,
        match="^V2-E-DECLARED-SCHEMA-GRAPH-MISMATCH$",
    ):
        v2.validate_schema_derived_graph(
            schemas, edges, declared_edge_table=declared
        )


def test_schema_graph_rejects_self_and_reciprocal_edges_from_real_annotations() -> None:
    schemas = v2.build_runtime_schemas()
    edges = v2.derive_reviewed_edge_table(schemas)
    self_edge = next(row for row in edges if "*" not in row["schema_field_path"])
    field = _schema_field(
        _schema_for_edge(schemas, self_edge), self_edge["schema_field_path"]
    )
    field["x-toe-hash-edge"]["referenced_artifact_type"] = self_edge[
        "containing_artifact_type"
    ]
    self_edges = v2.derive_reviewed_edge_table(schemas)
    with pytest.raises(
        v2.V2PreparationError,
        match="^V2-E-SCHEMA-GENERATION-ORDER-MISMATCH$",
    ):
        v2.validate_schema_derived_graph(schemas, self_edges)

    schemas = v2.build_runtime_schemas()
    edges = v2.derive_reviewed_edge_table(schemas)
    containing_types = {row["containing_artifact_type"] for row in edges}
    forward = next(
        row
        for row in edges
        if "*" not in row["schema_field_path"]
        and row["referenced_artifact_type"] in containing_types
        and any(
            candidate["containing_artifact_type"]
            == row["referenced_artifact_type"]
            and "*" not in candidate["schema_field_path"]
            for candidate in edges
        )
    )
    reverse_field_edge = next(
        row
        for row in edges
        if row["containing_artifact_type"]
        == forward["referenced_artifact_type"]
        and "*" not in row["schema_field_path"]
    )
    reverse_field = _schema_field(
        _schema_for_edge(schemas, reverse_field_edge),
        reverse_field_edge["schema_field_path"],
    )
    reverse_field["x-toe-hash-edge"]["referenced_artifact_type"] = forward[
        "containing_artifact_type"
    ]
    reciprocal_edges = v2.derive_reviewed_edge_table(schemas)
    with pytest.raises(
        v2.V2PreparationError,
        match=r"^V2-E-(?:LATER-PHASE-REFERENCE|SCHEMA-GENERATION-ORDER-MISMATCH)$",
    ):
        v2.validate_schema_derived_graph(schemas, reciprocal_edges)

    with pytest.raises(
        v2.V2PreparationError,
        match="^V2-E-SCHEMA-GENERATION-ORDER-MISMATCH$",
    ):
        v2._topological_sort({"A": {"B"}, "B": {"C"}, "C": {"A"}})


@pytest.mark.parametrize(
    ("mutation", "expected_code"),
    [
        (
            "declared_graph_differs_from_schema_graph",
            "V2-E-DECLARED-SCHEMA-GRAPH-MISMATCH",
        ),
        (
            "schema_graph_differs_from_generation_order",
            "V2-E-SCHEMA-GENERATION-ORDER-MISMATCH",
        ),
        ("undeclared_hash_bearing_field", "V2-E-HASH-FIELD-UNDECLARED"),
        ("later_phase_artifact_required_too_early", "V2-E-LATER-PHASE-REFERENCE"),
    ],
)
def test_graph_and_generation_order_permanent_controls_have_specific_codes(
    mutation: str, expected_code: str
) -> None:
    assert v2._observe_v2_control(mutation) == expected_code


@pytest.mark.parametrize("branch", ["COMPLETE", "POST_GENERATION_BLOCKED"])
def test_complete_and_post_generation_blocked_models_are_satisfiable(
    branch: str,
) -> None:
    fixture = v2.build_lifecycle_fixture(branch)
    assert fixture["branch"] == branch
    assert v2.validate_lifecycle_fixture(fixture) is None

    schemas = v2.build_runtime_schemas()
    for artifact_type, schema_name in fixture["schema_names"].items():
        document = fixture["documents"][artifact_type]
        Draft202012Validator(schemas[schema_name]).validate(document)
        assert fixture["artifact_bytes"][artifact_type] == (
            v2._history_witness()["set_bytes"]
            if artifact_type == "HISTORY_SHARD"
            else _encoded_document_bytes(artifact_type, document)
        )
    for event in fixture["trace_documents"]:
        Draft202012Validator(schemas["runtime_trace_event"]).validate(event)

    ledger = fixture["generation_ledger"]
    assert len(ledger) == len(set(ledger))
    assert ledger == v2._full_generation_ledger()
    assert set(ledger) == {
        node
        for node, (_, _, kind) in v2.ARTIFACT_PHASES.items()
        if kind != "EXTERNAL"
    }
    assert fixture["artifact_generation_ledger"] == (
        v2._physical_generation_ledger()
    )
    assert fixture["artifact_generation_ledger"] == list(
        fixture["artifact_bytes"]
    )
    assert [v2.ARTIFACT_PHASES[node][1] for node in ledger] == sorted(
        v2.ARTIFACT_PHASES[node][1] for node in ledger
    )
    assert ledger.index("SOURCE_MANIFEST") < ledger.index("CONSUMER_MAP")
    assert ledger.index("VALIDATION_REPORT") < ledger.index("RUNTIME_MANIFEST")
    assert ledger.index("RUNTIME_MANIFEST") < ledger.index("EXECUTION_REPORT")
    assert ledger.index("EXECUTION_REPORT") < ledger.index("TERMINAL_ENVELOPE")
    assert ledger.index("TERMINAL_ENVELOPE") < ledger.index("INDEPENDENT_REVIEW")

    documents = fixture["documents"]
    statuses = (
        documents["RUNTIME_MANIFEST"]["status"],
        documents["EXECUTION_REPORT"]["status"],
        documents["TERMINAL_ENVELOPE"]["candidate_status"],
        documents["INDEPENDENT_REVIEW"]["decision"],
    )
    if branch == "COMPLETE":
        assert statuses == (
            "CANDIDATE_COMPLETE",
            "STAGE_A_CANDIDATE_COMPLETE",
            "STAGE_A_CANDIDATE_COMPLETE_PENDING_INDEPENDENT_REVIEW",
            "ACCEPT_STAGE_A_CANDIDATE_ONLY",
        )
        assert not documents["RUNTIME_MANIFEST"]["block_reason_codes"]
    else:
        assert statuses == (
            "B_BLOCKED_CANDIDATE_PRESERVED",
            "B_BLOCKED_CANDIDATE_PRESERVED",
            "B_BLOCKED_STAGE_A_CANDIDATE_PRESERVED",
            "B_BLOCKED",
        )
        assert documents["RUNTIME_MANIFEST"]["block_reason_codes"]
        assert documents["EXECUTION_REPORT"]["block_reason_codes"]
        assert documents["TERMINAL_ENVELOPE"]["block_reason_codes"]


def test_inherited_artifacts_validate_and_use_their_exact_encoded_bytes() -> None:
    fixture = v2.build_lifecycle_fixture("COMPLETE")
    schemas = v2.build_runtime_schemas()
    inherited = {
        "HISTORY_SHARD": "history_shard_record",
        "CUSTODY_MANIFEST": "legacy_byte_custody_manifest",
        "LEGACY_RECONSTRUCTION": "compatibility_reconstruction_result",
        "HISTORY_INDEX": "history_index",
        "CURRENT_PROJECTION": "current_projection",
    }
    assert {
        artifact: fixture["schema_names"][artifact] for artifact in inherited
    } == inherited
    for artifact_type, schema_name in inherited.items():
        document = fixture["documents"][artifact_type]
        Draft202012Validator(schemas[schema_name]).validate(document)
        if artifact_type != "HISTORY_SHARD":
            assert fixture["artifact_bytes"][artifact_type] == (
                _encoded_document_bytes(artifact_type, document)
            )

    shard = fixture["documents"]["HISTORY_SHARD"]
    payload = base64.b64decode(
        shard["payload_canonical_json_utf8_base64"], validate=True
    )
    assert shard["payload_size_bytes"] == len(payload)
    assert shard["payload_sha256"] == v2.sha256(payload)
    assert fixture["history_record_count"] == 4_691
    assert fixture["history_shard_count"] == len(
        fixture["history_shard_members"]
    )
    assert fixture["history_shard_count"] == len(
        fixture["documents"]["HISTORY_INDEX"]["shards"]
    )
    observed_records = 0
    for descriptor in fixture["documents"]["HISTORY_INDEX"]["shards"]:
        raw = fixture["history_shard_members"][descriptor["path"]]
        assert len(raw) <= 5_242_880
        assert raw.endswith(b"\n") and b"\r" not in raw
        assert descriptor["sha256"] == v2.sha256(raw)
        assert descriptor["uncompressed_size_bytes"] == len(raw)
        lines = raw[:-1].split(b"\n")
        assert descriptor["record_count"] == len(lines)
        observed_records += len(lines)
        ids = []
        for line in lines:
            record = json.loads(line)
            assert _compact_json_bytes(record) == line
            Draft202012Validator(schemas["history_shard_record"]).validate(
                record
            )
            ids.append(record["record_id"])
        assert ids == sorted(ids)
        assert descriptor["first_record_id"] == ids[0]
        assert descriptor["last_record_id"] == ids[-1]
        assert descriptor["record_id_root_sha256"] == v2.sha256(
            "\n".join(ids).encode("utf-8")
        )
    assert observed_records == 4_691


def test_history_index_target_mutation_is_caught_by_instance_hash_graph() -> None:
    fixture = v2.build_lifecycle_fixture("COMPLETE")
    assert v2.validate_lifecycle_fixture(fixture) is None
    history_index = fixture["documents"]["HISTORY_INDEX"]
    history_index["consumer_source_map_pointer"]["sha256"] = "0" * 64
    fixture["artifact_bytes"]["HISTORY_INDEX"] = v2.canonical_json_bytes(
        history_index
    )
    assert v2.validate_lifecycle_fixture(fixture) == (
        "V2-E-INSTANCE-HASH-GRAPH-MISMATCH"
    )


@pytest.mark.parametrize(
    ("field", "artifact_types"),
    [
        (
            "reviewed_contract",
            ("EXECUTION_PREFLIGHT_ATTESTATION", "SOURCE_MANIFEST"),
        ),
        (
            "schema_bundle",
            (
                "EXECUTION_PREFLIGHT_ATTESTATION",
                "SOURCE_MANIFEST",
                "REVIEWED_TRUST_ANCHORS",
            ),
        ),
        (
            "protocol_bundle",
            (
                "EXECUTION_PREFLIGHT_ATTESTATION",
                "SOURCE_MANIFEST",
                "REVIEWED_TRUST_ANCHORS",
            ),
        ),
        (
            "implementation_inventory",
            ("EXECUTION_PREFLIGHT_ATTESTATION", "SOURCE_MANIFEST"),
        ),
    ],
)
def test_coordinated_local_rebind_cannot_replace_external_trust_roots(
    field: str, artifact_types: tuple[str, ...]
) -> None:
    fixture = v2.build_lifecycle_fixture("COMPLETE")
    assert v2.validate_lifecycle_fixture(fixture) is None
    documents = fixture["documents"]
    for artifact_type in artifact_types:
        identity = deepcopy(documents[artifact_type][field])
        identity["sha256"] = "f" * 64
        documents[artifact_type][field] = identity

    if "REVIEWED_TRUST_ANCHORS" in artifact_types:
        v2._refresh_document_bytes(fixture, "REVIEWED_TRUST_ANCHORS")
        documents["VALIDATION_REPORT"]["trust_anchor_sha256"] = v2.sha256(
            fixture["artifact_bytes"]["REVIEWED_TRUST_ANCHORS"]
        )
        v2._refresh_document_bytes(fixture, "VALIDATION_REPORT")
    v2._rebind_after_attestation(fixture)

    assert v2.validate_lifecycle_fixture(fixture) == (
        "V2-E-EXTERNAL-TRUST-BINDING-MISMATCH"
    )


def test_custody_gzip_reconstructs_the_exact_git_registry_bytes() -> None:
    fixture = v2.build_lifecycle_fixture("COMPLETE")
    source = _git_blob(v2.SOURCE_COMMIT, v2.REGISTRY_REL)
    payload = fixture["artifact_bytes"]["CUSTODY_PAYLOAD"]
    assert payload[:3] == b"\x1f\x8b\x08"
    assert payload[3] == 0
    assert payload[4:8] == b"\0\0\0\0"
    assert payload[8] == 2
    assert payload[9] == 255
    assert gzip.decompress(payload) == source

    manifest = fixture["documents"]["CUSTODY_MANIFEST"]
    assert manifest["payload_identity"]["compressed_sha256"] == v2.sha256(
        payload
    )
    assert manifest["payload_identity"]["compressed_size_bytes"] == len(payload)
    assert manifest["reconstruction_requirement"]["decompressed_sha256"] == (
        v2.sha256(source)
    )
    assert manifest["reconstruction_requirement"][
        "decompressed_size_bytes"
    ] == len(source)
    reconstruction = fixture["documents"]["LEGACY_RECONSTRUCTION"]
    assert reconstruction["custody_payload_identity"]["sha256"] == v2.sha256(
        payload
    )
    assert reconstruction["reconstruction_identity"]["sha256"] == v2.sha256(
        source
    )


def test_coherent_preflight_commit_and_tree_rebinding_is_rejected() -> None:
    fixture = v2.build_lifecycle_fixture("COMPLETE")
    assert v2.validate_lifecycle_fixture(fixture) is None
    rebound_commit = "d" * 40
    rebound_tree = "e" * 40
    inventory = fixture["documents"]["PREFLIGHT_CONSUMER_INVENTORY"]
    attestation = fixture["documents"]["EXECUTION_PREFLIGHT_ATTESTATION"]
    source = fixture["documents"]["SOURCE_MANIFEST"]
    inventory["source_commit"] = rebound_commit
    inventory["source_tree"] = rebound_tree
    attestation["source_commit"] = rebound_commit
    attestation["source_tree"] = rebound_tree
    source["source_commit"] = rebound_commit
    v2._rebind_after_inventory(fixture)
    assert v2.validate_lifecycle_fixture(fixture) == (
        "V2-E-PREFLIGHT-SOURCE-COMMIT-MISMATCH"
    )


def test_independent_review_cannot_coherently_reuse_execution_inventory() -> None:
    fixture = v2.build_lifecycle_fixture("COMPLETE")
    assert v2.validate_lifecycle_fixture(fixture) is None
    preflight = fixture["documents"]["PREFLIGHT_CONSUMER_INVENTORY"]
    review_inventory = fixture["documents"][
        "INDEPENDENT_REVIEW_CONSUMER_INVENTORY"
    ]
    review = fixture["documents"]["INDEPENDENT_REVIEW"]
    review_inventory["consumer_identity_root_sha256"] = preflight[
        "consumer_identity_root_sha256"
    ]
    review_inventory["runtime_required_identity_root_sha256"] = preflight[
        "runtime_required_identity_root_sha256"
    ]
    review_inventory["baseline_delta_root_sha256"] = preflight[
        "baseline_delta_root_sha256"
    ]
    fixture["artifact_bytes"]["INDEPENDENT_REVIEW_CONSUMER_INVENTORY"] = (
        v2.canonical_json_bytes(review_inventory)
    )
    review["review_inventory"] = _artifact_identity(
        "review/consumer_inventory.json",
        fixture["artifact_bytes"]["INDEPENDENT_REVIEW_CONSUMER_INVENTORY"],
    )
    review["independent_rescan_root_sha256"] = preflight[
        "consumer_identity_root_sha256"
    ]
    fixture["artifact_bytes"]["INDEPENDENT_REVIEW"] = v2.canonical_json_bytes(
        review
    )
    assert v2.validate_lifecycle_fixture(fixture) == (
        "V2-E-REVIEW-CONSUMER-RESCAN-REQUIRED"
    )


@pytest.mark.parametrize(
    ("field", "replacement", "expected_code"),
    [
        ("semantic_parity", False, "V2-E-RUNTIME-TRACE-PARITY-MISMATCH"),
        (
            "candidate_result_sha256",
            "f" * 64,
            "V2-E-RUNTIME-TRACE-PARITY-MISMATCH",
        ),
        (
            "consumer_path",
            "invented/runtime_consumer.py",
            "V2-E-RUNTIME-TRACE-UNMATCHED",
        ),
        (
            "consumer_source_sha256",
            "f" * 64,
            "V2-E-RUNTIME-TRACE-UNMATCHED",
        ),
        (
            "operation_class",
            "READ_HISTORICAL_RECORD",
            "V2-E-RUNTIME-TRACE-UNMATCHED",
        ),
    ],
)
def test_runtime_trace_requires_semantic_result_and_consumer_field_parity(
    field: str, replacement: Any, expected_code: str
) -> None:
    fixture = v2.build_lifecycle_fixture("COMPLETE")
    assert v2.validate_lifecycle_fixture(fixture) is None
    fixture["trace_documents"][0][field] = replacement
    _rebind_trace_and_terminal_chain(fixture)
    assert v2.validate_lifecycle_fixture(fixture) == expected_code


@pytest.mark.parametrize(
    ("failure", "expected_code"),
    [
        ("registry", "V2-E-SOURCE-REGISTRY-MISMATCH"),
        ("inventory", "V2-E-CONSUMER-RESCAN-FAILURE"),
        ("graph", "V2-E-SCHEMA-GENERATION-ORDER-MISMATCH"),
        ("schema", "V2-E-HASH-FIELD-UNDECLARED"),
    ],
)
def test_preflight_failures_are_bounded_diagnostic_only(
    tmp_path: Path, failure: str, expected_code: str
) -> None:
    prototype_root = tmp_path / "prototype-must-not-exist"
    exit_code, diagnostic, raw = v2.simulate_preflight_failure(
        prototype_root, failure
    )
    assert exit_code != 0
    assert diagnostic["error_code"] == expected_code
    assert diagnostic["exit_code"] == exit_code
    assert diagnostic["candidate_set_created"] is False
    assert diagnostic["prototype_run_root_created"] is False
    assert diagnostic["controls_observed"] == 0
    assert raw == v2.canonical_json_bytes(diagnostic)
    assert len(raw) <= 16_384
    assert not prototype_root.exists()
    Draft202012Validator(
        v2.build_runtime_schemas()["preflight_diagnostic"]
    ).validate(diagnostic)


def test_exact_twelve_legacy_and_fifteen_v2_controls_are_frozen() -> None:
    legacy = _normalise_controls(v2.LEGACY_DAG_CONTROLS)
    successor = _normalise_controls(v2.V2_NEGATIVE_CONTROLS)
    assert legacy == EXPECTED_LEGACY_DAG_CONTROLS
    assert successor == EXPECTED_V2_NEGATIVE_CONTROLS
    assert len(legacy) == 12
    assert len(successor) == 15

    combined = legacy + successor
    assert len(combined) == len({row[0] for row in combined}) == 27
    assert len(combined) == len({row[1] for row in combined}) == 27
    assert len(combined) == len({row[2] for row in combined}) == 27


def test_all_permanent_controls_run_from_fresh_positive_fixtures() -> None:
    results = v2.run_permanent_negative_controls()
    expected = EXPECTED_LEGACY_DAG_CONTROLS + EXPECTED_V2_NEGATIVE_CONTROLS
    assert len(results) == len(expected) == 27

    for result, (control_id, mutation, expected_code) in zip(results, expected):
        assert result["control_id"] == control_id
        assert result["mutation"] == mutation
        assert result["expected_error_code"] == expected_code
        assert result["observed_error_code"] == expected_code
        assert result["passed"] is True
        assert result["baseline_recreated"] is True
        assert result["subsequent_controls_unmodified"] is True
        assert result["baseline_root_sha256_before"] == result[
            "baseline_root_sha256_after"
        ]

    by_mutation = {result["mutation"]: result for result in results}
    for mutation in (
        "consumer_map_truncated_to_one_row",
        "trace_truncated_to_match_consumer_map",
        "consumer_map_and_trace_locally_rebound",
    ):
        assert by_mutation[mutation]["local_candidate_hashes_rebound"] is True
    assert by_mutation["terminal_envelope_hashes_itself"][
        "observed_error_code"
    ] == "V1-E-TERMINAL-ENVELOPE-SELF-REFERENCE"
    assert by_mutation["execution_report_and_terminal_bind_reciprocally"][
        "observed_error_code"
    ] == "V1-E-EXECUTION-TERMINAL-CYCLE"


@pytest.mark.parametrize(
    ("_control_id", "mutation", "expected_code"),
    EXPECTED_LEGACY_DAG_CONTROLS,
)
def test_each_legacy_control_exercises_the_real_lifecycle_validator(
    monkeypatch: pytest.MonkeyPatch,
    _control_id: str,
    mutation: str,
    expected_code: str,
) -> None:
    real_validator = v2.validate_lifecycle_fixture
    observed_branches: list[str] = []

    def observed_validator(fixture: dict[str, Any]) -> str | None:
        observed_branches.append(str(fixture["branch"]))
        return real_validator(fixture)

    monkeypatch.setattr(v2, "validate_lifecycle_fixture", observed_validator)
    assert v2._observe_legacy_control(mutation) == expected_code
    assert observed_branches == ["COMPLETE"]


@pytest.mark.parametrize(
    ("_control_id", "mutation", "expected_code"),
    EXPECTED_V2_NEGATIVE_CONTROLS[4:],
)
def test_inventory_and_trace_mutations_defeat_candidate_local_rebinding(
    _control_id: str, mutation: str, expected_code: str
) -> None:
    assert v2._observe_v2_control(mutation) == expected_code


def test_source_commit_legacy_scan_has_unique_stable_typed_identities() -> None:
    inventory = v2.scan_legacy_consumer_surface(v2.SOURCE_COMMIT)
    rows = inventory["consumers"]
    assert inventory["git_commit"] == v2.SOURCE_COMMIT
    assert inventory["consumer_count"] == len(rows) == 522
    assert inventory["runtime_required_count"] == 486
    assert inventory["non_runtime_count"] == 36
    assert len(rows) == len({row["consumer_id"] for row in rows})

    for row in rows:
        assert row["consumer_category"] in v2.CONSUMER_CATEGORIES
        assert row["operation_class"] in v2.OPERATION_CLASSES
        assert row["discovery_mechanism"] in v2.DISCOVERY_MECHANISMS
        assert re.fullmatch(r"[0-9a-f]{64}", row["statement_or_call_site_sha256"])
        assert row["statement_or_call_site_sha256"] == row[
            "statement_or_callsite_sha256"
        ]
        assert isinstance(row["runtime_required"], bool)
        identity = {
            "repository_relative_path": row["path"],
            "consumer_category": row["consumer_category"],
            "operation_class": row["operation_class"],
            "discovery_mechanism": row["discovery_mechanism"],
            "statement_or_call_site_sha256": row[
                "statement_or_call_site_sha256"
            ],
        }
        expected_id = "lcc2:" + v2.sha256(
            b"LOOP_CONTROL_CONSUMER_ID_v2\0" + _compact_json_bytes(identity)
        )
        assert row["consumer_id"] == expected_id
    assert inventory["runtime_required_count"] == sum(
        row["runtime_required"] for row in rows
    )


def test_consumer_inventory_algorithm_and_reconciliation_are_external() -> None:
    contract = v2.build_contract()
    algorithm = contract["consumer_inventory_algorithm"]
    assert algorithm["authoritative_input"] == (
        "EXACT_GIT_COMMIT_TREE_AND_BLOBS_LOADED_WITH_GIT_LS_TREE_AND_CAT_FILE"
    )
    assert algorithm["candidate_or_worktree_input_permitted"] is False
    assert algorithm["consumer_categories"] == v2.CONSUMER_CATEGORIES
    assert algorithm["operation_classes"] == v2.OPERATION_CLASSES
    assert algorithm["runtime_required_categories"] == (
        v2.RUNTIME_REQUIRED_CATEGORIES
    )
    assert algorithm["runtime_required_is_derived_not_candidate_supplied"] is True
    assert algorithm["identity_fields"] == [
        "repository_relative_path",
        "consumer_category",
        "operation_class",
        "discovery_mechanism",
        "statement_or_call_site_sha256",
    ]

    reconciliation = contract["consumer_inventory_reconciliation"]
    assert set(reconciliation) == EXPECTED_RECONCILIATION_KEYS
    assert all(reconciliation.values())


def test_historical_520_is_evidence_not_a_future_execution_expectation() -> None:
    contract = v2.build_contract()
    historical = contract["consumer_inventory_historical_evidence"]
    assert historical["baseline"] == {
        "baseline_commit": "f9168ab5f566fb2019b9e76e68ff3e60e5c0dc52",
        "path_count": 496,
        "runtime_required_path_count": 470,
        "nonruntime_path_count": 26,
    }
    reviewed = historical["accepted_v1_review_scan"]
    assert reviewed["scan_commit"] == (
        "6ce5f8389a8b4ac0cba2ab68ba9f4bb1e39743df"
    )
    assert reviewed["evidence_commit"] == v2.SOURCE_COMMIT
    assert reviewed["path_count"] == 520
    assert reviewed["runtime_required_path_count"] == 485
    assert reviewed["nonruntime_path_count"] == 35
    assert reviewed["added_path_count"] == 24
    assert reviewed["removed_path_count"] == 0
    assert reviewed["changed_baseline_path_count"] == 3

    source = historical["v2_preparation_source_scan"]
    assert source["scan_commit"] == v2.SOURCE_COMMIT
    assert source["path_count"] == 522
    assert source["runtime_required_path_count"] == 486
    assert source["nonruntime_path_count"] == 36
    assert source["evidence_only_not_future_expectation"] is True
    assert historical["future_execution_uses_fresh_preflight_counts"] is True
    assert historical["no_historical_count_is_normative_for_future_execution"] is True
    assert historical[
        "counts_are_path_level_not_v2_callsite_identity_counts"
    ] is True

    forbidden_keys = {
        "expected_consumer_count",
        "candidate_expected_consumer_count",
        "current_expected_consumer_count",
    }
    for path, value in _walk(contract):
        if path and path[-1] in forbidden_keys:
            pytest.fail(f"candidate-local count at {'/'.join(path)}: {value}")

    frozen_counts = {496, 520, 485, 35}
    for schema_name, schema in v2.build_runtime_schemas().items():
        for path, value in _walk(schema):
            if not isinstance(value, Mapping) or "const" not in value:
                continue
            field_path = "/".join(path).lower()
            if ("consumer" in field_path or "runtime_required" in field_path) and value[
                "const"
            ] in frozen_counts:
                pytest.fail(
                    f"historical count frozen in {schema_name}/{field_path}"
                )


def test_packet_is_preparation_only_and_protected_surfaces_are_unchanged() -> None:
    packet = v2.build_packet()
    assert packet["source_commit"] == AUTHORITATIVE_SOURCE_COMMIT
    assert packet["authorization"] == {
        "implementation_change_authorized": False,
        "independent_review_required": True,
        "maintenance_target_rotation_authorized": False,
        "prototype_execution_authorized": False,
        "registry_cutover_authorized": False,
        "registry_migration_execution_authorized": False,
        "scientific_target_rotation_authorized": False,
        "stage_a_authorized": False,
        "stage_b_authorized": False,
        "unit_ledger_execution_authorized": False,
    }
    assert packet["boundary"]["candidate_artifacts_created"] is False
    assert packet["boundary"]["prototype_execution_attempted"] is False
    assert packet["boundary"]["legacy_monolith_modified_or_retired"] is False
    assert packet["boundary"][
        "v1_preparation_or_blocked_review_amended"
    ] is False

    protected = [
        v2.REGISTRY_REL,
        v2.MAINTENANCE_AUTHORITY_REL,
        v2.AUTHORITATIVE_SURFACES_REL,
        *v2.AUTHORIZED_IMPLEMENTATION_PATHS,
    ]
    changed = _git(
        "diff", "--name-only", v2.SOURCE_COMMIT, "--", *protected
    ).stdout.decode("utf-8")
    assert changed.strip() == ""
    for relative in v2.PRODUCTION_LAYOUT_PATHS:
        assert not (v2.REPO_ROOT / relative).exists()

    contract = v2.build_contract()
    assert contract["supersession"][
        "preserves_v1_preparation_and_blocked_review"
    ] is True
    assert contract["supersession"]["v1_artifacts_amended_or_replaced"] is False
    assert contract["nonpromotion"]["stage_a_execution_performed"] is False
    assert contract["nonpromotion"]["stage_b_authorized"] is False


def test_v2_integration_and_lean_certificate_bind_generated_evidence() -> None:
    relative_test = (
        "formal/python/tests/"
        "test_loop_control_registry_sharding_read_only_prototype_execution_packet_v2.py"
    )
    manifest = _load(
        v2.REPO_ROOT / "formal/docs/release/GOVERNANCE_TEST_MANIFEST_v1.json"
    )
    assert manifest["test_tiers"][relative_test] == "TIER_INTEGRITY"
    integrity = manifest["groups"]["integrity_gates"]
    assert integrity["expected_count"] == len(integrity["tests"]) == 69
    assert relative_test in integrity["tests"]
    assert integrity["expected_sha256"] == v2.sha256(
        "\n".join(integrity["tests"]).encode("utf-8")
    )

    aggregate = (
        v2.REPO_ROOT / "formal/toe_formal/ToeFormalAll.lean"
    ).read_text(encoding="utf-8")
    assert (
        "import ToeFormal.Release."
        "LoopControlRegistryShardingReadOnlyPrototypeExecutionPacketV2"
    ) in aggregate
    assert "def trackedModuleCount : Nat := 1066" in aggregate

    lean = (
        v2.REPO_ROOT
        / "formal/toe_formal/ToeFormal/Release/"
        "LoopControlRegistryShardingReadOnlyPrototypeExecutionPacketV2.lean"
    ).read_text(encoding="utf-8")
    contract = v2.build_contract()
    for token in (
        v2.SOURCE_COMMIT,
        v2.sha256(v2.PACKET_PATH.read_bytes()),
        v2.sha256(v2.CONTRACT_PATH.read_bytes()),
        contract["reviewed_schema_hash_edge_table"]["root_sha256"],
        "def existingStageAControlCount : Nat := 76",
        "def permanentSuccessorRegressionCount : Nat := 27",
        "def stageAAuthorized : Bool := false",
        "def stageBAuthorized : Bool := false",
    ):
        assert token in lean
