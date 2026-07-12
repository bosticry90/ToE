"""Independent blocked review of the frozen Stage-A v2 preparation contract.

This reviewer deliberately does not import the v2 preparation generator.  It
loads the exact preparation commit through Git objects, walks the embedded
schemas itself, rescans repository consumer call sites with a separately
implemented full-tree scanner, reconstructs the complete custody model, and
checks the four production implementation paths.  It never creates a
prototype root and never invokes Stage A.
"""

from __future__ import annotations

import argparse
import base64
from concurrent.futures import ThreadPoolExecutor
from copy import deepcopy
import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from typing import Any, Iterable

from jsonschema.validators import validator_for

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
PREPARATION_COMMIT = "0138ba751ef2ae1b08347a3089da077c5a694550"
PREPARATION_TREE = "f193aac1c15b082e6c5500dd6a426cf13871a9c1"
SOURCE_COMMIT = "81a3555a1f83a37ec01bacc247f45d1a5bfe8430"
CAPTURED_AT_UTC = "2026-07-12T00:00:00Z"

PACKET_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_PACKET_"
    "20260712_v2.json"
)
CONTRACT_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_CONTRACT_"
    "BUNDLE_20260712_v2.json"
)
GENERATOR_REL = (
    "formal/python/tools/"
    "loop_control_registry_sharding_read_only_prototype_execution_packet_v2.py"
)
TEST_REL = (
    "formal/python/tests/"
    "test_loop_control_registry_sharding_read_only_prototype_execution_packet_v2.py"
)
LEAN_REL = (
    "formal/toe_formal/ToeFormal/Release/"
    "LoopControlRegistryShardingReadOnlyPrototypeExecutionPacketV2.lean"
)
OUTPUT_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_PACKET_"
    "INDEPENDENT_REVIEW_20260712_v2.json"
)
OUTPUT_PATH = REPO_ROOT / OUTPUT_REL

REGISTRY_REL = "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
BASELINE_CONSUMER_REL = (
    "formal/docs/release/LOOP_CONTROL_REGISTRY_CONSUMER_SOURCE_MAP_20260711_v1.json"
)
MAINTENANCE_REL = "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v0.json"
AUTHORITY_REL = "formal/docs/release/CURRENT_AUTHORITATIVE_SURFACES_v0.md"
PROTOTYPE_REL = "formal/scratch/loop_control_registry_v1_prototype"
GOVERNANCE_MANIFEST_REL = "formal/docs/release/GOVERNANCE_TEST_MANIFEST_v1.json"

PACKET_SHA256 = "8381ae2101610eab7ae307e4c3849efbe1a1d9786b4edee7702f70d2662b723a"
CONTRACT_SHA256 = "36d7bdfe8f03e0e6cceb2fd653b98f0f0f26fcadaf40ff53a0dc2450b4f04432"
EDGE_ROOT_SHA256 = "55c46d8c7347473e6c6578e4f79fc8f5b670a1172f512903cfabe7d5ce90988c"
REGISTRY_SHA256 = "eda451133e8bbfe1ba0e815b29735f874e8b33e61d7fc5085999c4ba38df0543"

REGENERATED_PACKET_SHA256 = (
    "fbbe09b35ba567a8686094fd66a96cfb854410d8b72c223a2bbb709c5ba1f555"
)
REGENERATED_CONTRACT_SHA256 = (
    "081e666a1cd4d5b06f27764249418b4cc55563b25426821c73b67d516dc45323"
)

SCIENTIFIC_TARGET = "execute_pillar_seam_unit_mapping_ledger_v0"
MAINTENANCE_TARGET = (
    "prepare_loop_control_registry_sharding_and_current_projection_packet_v0"
)
SUCCESSOR_TARGET = (
    "prepare_loop_control_registry_sharding_read_only_prototype_execution_packet_v3"
)

PREPARATION_INPUTS: dict[str, tuple[str, str, int]] = {
    PACKET_REL: (
        PACKET_SHA256,
        "11ec2c182bf7b85ce71eca728d12faa2b9a7bb4a",
        2_173,
    ),
    CONTRACT_REL: (
        CONTRACT_SHA256,
        "3d91b6ec401460d4c10506e4025ef0fd831dbc88",
        699_122,
    ),
    GENERATOR_REL: (
        "f003f1f4bb7648e2ea7f944267443a424f3e439d9b26ec202763ec8e3f028c38",
        "273d91a8d79bb256104897ef91a1475a64b8c642",
        283_437,
    ),
    TEST_REL: (
        "2915c82ade1d63a699524a2275425a82bd69ad1bfff0c4cfb594deb470612737",
        "a11a81fe9cb647724664985904dd5990f5d3d816",
        46_233,
    ),
    LEAN_REL: (
        "8eaafb738a2296327cb6e086195a4696c72195050d54ae174a18a87d76df50d9",
        "028481b1701832928c8dfb7788128e80ceb5a23e",
        3_952,
    ),
}

AUTHORIZED_IMPLEMENTATION_PATHS = [
    "formal/python/tools/loop_control_registry_sharding_read_only_prototype_execution.py",
    "formal/python/toe/loop_control_registry_v1.py",
    "formal/python/toe/loop_control_registry_v1_validator.py",
    "formal/python/tests/test_loop_control_registry_v1_production_controls.py",
]

NONLITERAL_READERS = [
    "formal/python/tests/test_loop_control_registry_envelope_integrity_gate.py",
    "formal/python/tests/test_loop_control_registry_integrity_repair_custody_gate.py",
    "formal/python/tools/loop_control_registry_sharding_guardrail.py",
]

RUNTIME_REQUIRED_CATEGORIES = {
    "DIRECT_READER",
    "INDIRECT_API_CONSUMER",
    "DYNAMIC_READER",
    "WRITER",
}

SCHEMA_ARTIFACT_TYPES = {
    "candidate_consumer_map": "CONSUMER_MAP",
    "compatibility_reconstruction_result": "LEGACY_RECONSTRUCTION",
    "control_evidence": "CONTROL_EVIDENCE",
    "current_projection": "CURRENT_PROJECTION",
    "execution_preflight_attestation": "EXECUTION_PREFLIGHT_ATTESTATION",
    "execution_report": "EXECUTION_REPORT",
    "execution_source_manifest": "SOURCE_MANIFEST",
    "history_index": "HISTORY_INDEX",
    "history_shard_record": "HISTORY_SHARD",
    "independent_review_binding": "INDEPENDENT_REVIEW",
    "independent_review_consumer_inventory": "INDEPENDENT_REVIEW_CONSUMER_INVENTORY",
    "legacy_byte_custody_manifest": "CUSTODY_MANIFEST",
    "preflight_consumer_inventory": "PREFLIGHT_CONSUMER_INVENTORY",
    "preflight_diagnostic": "PREFLIGHT_DIAGNOSTIC",
    "reviewed_trust_anchors": "REVIEWED_TRUST_ANCHORS",
    "rollback_inventory": "ROLLBACK_INVENTORY",
    "runtime_manifest": "RUNTIME_MANIFEST",
    "runtime_trace_event": "RUNTIME_TRACE",
    "runtime_trace_manifest": "RUNTIME_TRACE_MANIFEST",
    "terminal_envelope": "TERMINAL_ENVELOPE",
    "validation_report": "VALIDATION_REPORT",
    "writer_probe": "WRITER_PROBE",
}


class IndependentV2ReviewError(ValueError):
    pass


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def compact_json_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        allow_nan=False,
        ensure_ascii=False,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("utf-8")


def canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(
            value,
            allow_nan=False,
            ensure_ascii=False,
            indent=2,
            sort_keys=True,
        )
        + "\n"
    ).encode("utf-8")


def _strict_json(raw: bytes) -> Any:
    if raw.startswith(b"\xef\xbb\xbf") or b"\r" in raw or not raw.endswith(b"\n"):
        raise IndependentV2ReviewError("reviewed JSON is not canonical LF UTF-8")
    value = json.loads(raw.decode("utf-8"), parse_constant=lambda value: (_ for _ in ()).throw(ValueError(value)))
    if canonical_json_bytes(value) != raw:
        raise IndependentV2ReviewError("reviewed JSON is not canonical")
    return value


_BLOB_CACHE: dict[tuple[str, str], bytes] = {}


def _git_blob(commit: str, relative: str) -> bytes:
    key = (commit, relative)
    if key not in _BLOB_CACHE:
        completed = subprocess.run(
            ["git", "cat-file", "blob", f"{commit}:{relative}"],
            cwd=REPO_ROOT,
            capture_output=True,
            check=True,
        )
        _BLOB_CACHE[key] = completed.stdout
    return _BLOB_CACHE[key]


def _git_oid(commit: str, relative: str) -> str:
    return subprocess.run(
        ["git", "rev-parse", f"{commit}:{relative}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=True,
        text=True,
    ).stdout.strip()


def _git_path_exists(commit: str, relative: str) -> bool:
    return subprocess.run(
        ["git", "cat-file", "-e", f"{commit}:{relative}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
    ).returncode == 0


def _preparation_input_evidence() -> dict[str, dict[str, Any]]:
    evidence: dict[str, dict[str, Any]] = {}
    for relative, (expected_sha, expected_oid, expected_size) in PREPARATION_INPUTS.items():
        raw = _git_blob(PREPARATION_COMMIT, relative)
        observed = (sha256(raw), _git_oid(PREPARATION_COMMIT, relative), len(raw))
        if observed != (expected_sha, expected_oid, expected_size):
            raise IndependentV2ReviewError(f"preparation input drift: {relative}")
        evidence[relative] = {
            "git_blob": observed[1],
            "path": relative,
            "sha256": observed[0],
            "size_bytes": observed[2],
            "source_commit": PREPARATION_COMMIT,
        }
    return evidence


def _escape_pointer(token: str) -> str:
    return token.replace("~", "~0").replace("/", "~1")


def _hash_bearing(name: str, schema: Any) -> bool:
    if not isinstance(schema, dict):
        return False
    constant = schema.get("const")
    constant_hash = (
        isinstance(constant, str)
        and len(constant) == 64
        and all(character in "0123456789abcdef" for character in constant)
    )
    pattern = schema.get("pattern")
    return (
        name == "sha256"
        or name.endswith("_sha256")
        or (isinstance(pattern, str) and "[0-9a-f]{64}" in pattern)
        or constant_hash
    )


def _schema_hash_fields(
    schema: dict[str, Any],
    *,
    reject_unannotated: bool = True,
    unannotated: list[dict[str, Any]] | None = None,
) -> list[dict[str, Any]]:
    observed: dict[tuple[str, str, str, str], dict[str, Any]] = {}

    def walk(value: Any, path: str, required: bool) -> None:
        if not isinstance(value, dict):
            return
        properties = value.get("properties")
        required_names = set(value.get("required", []))
        if isinstance(properties, dict):
            for name, child in properties.items():
                child_path = f"{path}/{_escape_pointer(name)}"
                child_required = required and name in required_names
                if _hash_bearing(name, child):
                    annotation = child.get("x-toe-hash-edge")
                    if not isinstance(annotation, dict):
                        if reject_unannotated:
                            raise IndependentV2ReviewError(
                                f"V2-E-HASH-FIELD-UNDECLARED:{child_path}"
                            )
                        if unannotated is not None:
                            unannotated.append(
                                {
                                    "field_name": name,
                                    "pattern": child.get("pattern"),
                                    "schema_field_path": child_path,
                                }
                            )
                        walk(child, child_path, child_required)
                        continue
                    key = (
                        child_path,
                        annotation["referenced_artifact_type"],
                        annotation["hash_semantics"],
                        annotation["target_resolver"],
                    )
                    observed[key] = {
                        "schema_field_path": child_path,
                        **annotation,
                        "required_optional_status": (
                            "REQUIRED" if child_required else "CONDITIONAL_OR_OPTIONAL"
                        ),
                    }
                walk(child, child_path, child_required)
        if isinstance(value.get("items"), dict):
            walk(
                value["items"],
                f"{path}/*",
                required and value.get("minItems", 0) > 0,
            )
        if isinstance(value.get("prefixItems"), list):
            for child in value["prefixItems"]:
                walk(child, f"{path}/*", required)
        for keyword in ("allOf", "anyOf", "oneOf"):
            if isinstance(value.get(keyword), list):
                for child in value[keyword]:
                    walk(child, path, required)

    walk(schema, "", True)
    return [observed[key] for key in sorted(observed)]


def derive_schema_edge_table(
    contract: dict[str, Any],
    *,
    reject_unannotated: bool = True,
    unannotated: list[dict[str, Any]] | None = None,
) -> list[dict[str, Any]]:
    schemas = contract["runtime_schemas"]
    phases = {
        row["artifact_type"]: row for row in contract["generation_phase_table"]["rows"]
    }
    candidate_array = schemas["runtime_manifest"]["properties"]["candidate_artifacts"]
    required_dynamic_targets = {
        row["contains"]["properties"]["artifact_type"]["const"]
        for row in candidate_array.get("allOf", [])
        if row.get("minContains", 1) > 0
        and isinstance(row.get("contains"), dict)
        and isinstance(
            row["contains"].get("properties", {}).get("artifact_type"), dict
        )
        and isinstance(
            row["contains"]["properties"]["artifact_type"].get("const"), str
        )
    }
    if required_dynamic_targets != set(
        candidate_array.get("x-toe-required-artifact-types", [])
    ):
        raise IndependentV2ReviewError("dynamic artifact declaration mismatch")

    rows: list[dict[str, Any]] = []
    for schema_name in sorted(schemas):
        artifact = SCHEMA_ARTIFACT_TYPES[schema_name]
        if artifact == "PREFLIGHT_DIAGNOSTIC":
            continue
        containing = phases[artifact]
        schema_unannotated: list[dict[str, Any]] = []
        fields = _schema_hash_fields(
            schemas[schema_name],
            reject_unannotated=reject_unannotated,
            unannotated=schema_unannotated,
        )
        if unannotated is not None:
            unannotated.extend(
                {"schema_name": schema_name, **row} for row in schema_unannotated
            )
        for field in fields:
            declared_target = field["referenced_artifact_type"]
            targets = [declared_target]
            if declared_target == "DYNAMIC_CANDIDATE_ARTIFACT":
                targets = list(
                    candidate_array["items"]["properties"]["artifact_type"]["enum"]
                )
            for target in targets:
                referenced = phases[target]
                target_required = (
                    field["required_optional_status"] == "REQUIRED"
                    and (
                        declared_target != "DYNAMIC_CANDIDATE_ARTIFACT"
                        or target in required_dynamic_targets
                    )
                )
                applicability = (
                    "REQUIRED" if target_required else "CONDITIONAL_OR_OPTIONAL"
                )
                rows.append(
                    {
                        "blocked_path_applicability": applicability,
                        "complete_path_applicability": applicability,
                        "containing_artifact_type": artifact,
                        "containing_generation_ordinal": containing[
                            "generation_ordinal"
                        ],
                        "containing_generation_phase": containing[
                            "generation_phase"
                        ],
                        "containing_schema_id": schemas[schema_name]["$id"],
                        "hash_semantics": field["hash_semantics"],
                        "referenced_artifact_type": target,
                        "referenced_generation_ordinal": referenced[
                            "generation_ordinal"
                        ],
                        "referenced_generation_phase": referenced[
                            "generation_phase"
                        ],
                        "required_optional_status": applicability,
                        "schema_field_path": field["schema_field_path"],
                        "target_resolver": (
                            f"SIBLING_ARTIFACT_TYPE={target}"
                            if declared_target == "DYNAMIC_CANDIDATE_ARTIFACT"
                            else field["target_resolver"]
                        ),
                    }
                )
    return sorted(
        rows,
        key=lambda row: (
            row["containing_generation_ordinal"],
            row["containing_artifact_type"],
            row["schema_field_path"],
            row["referenced_artifact_type"],
        ),
    )


def _topological_order(graph: dict[str, set[str]]) -> list[str]:
    remaining = {node: set(dependencies) for node, dependencies in graph.items()}
    order: list[str] = []
    while remaining:
        ready = sorted(node for node, dependencies in remaining.items() if not dependencies)
        if not ready:
            break
        for node in ready:
            order.append(node)
            remaining.pop(node)
            for dependencies in remaining.values():
                dependencies.discard(node)
    return order


def _graph_review(contract: dict[str, Any]) -> dict[str, Any]:
    schemas = contract["runtime_schemas"]
    if set(schemas) != set(SCHEMA_ARTIFACT_TYPES):
        raise IndependentV2ReviewError("runtime schema catalog mismatch")
    for schema in schemas.values():
        validator_for(schema).check_schema(schema)
    unannotated: list[dict[str, Any]] = []
    derived = derive_schema_edge_table(
        contract,
        reject_unannotated=False,
        unannotated=unannotated,
    )
    declared = contract["reviewed_schema_hash_edge_table"]["rows"]
    edge_root = sha256(
        b"LOOP_CONTROL_V2_REVIEWED_SCHEMA_HASH_EDGE_TABLE\0"
        + b"\n".join(compact_json_bytes(row) for row in derived)
    )
    phases = contract["generation_phase_table"]["rows"]
    graph = {
        row["artifact_type"]: set()
        for row in phases
        if row["node_kind"] != "EXTERNAL"
        and row["artifact_type"] != "PREFLIGHT_DIAGNOSTIC"
    }
    self_edges = []
    later_edges = []
    for row in derived:
        source = row["containing_artifact_type"]
        target = row["referenced_artifact_type"]
        if source == target:
            self_edges.append([source, target])
        if row["referenced_generation_ordinal"] >= row["containing_generation_ordinal"]:
            later_edges.append(
                [source, row["schema_field_path"], target]
            )
        if source in graph and target in graph:
            graph[source].add(target)
    reciprocal = sorted(
        [source, target]
        for source, targets in graph.items()
        for target in targets
        if source < target and source in graph.get(target, set())
    )
    order = _topological_order(graph)
    topological_success = len(order) == len(graph) == len(set(order))
    return {
        "complete_branch_topological_sort_succeeds": topological_success,
        "contract_edge_count": len(declared),
        "contract_edge_root_sha256": contract["reviewed_schema_hash_edge_table"][
            "root_sha256"
        ],
        "contract_generation_order": contract["schema_derived_graph_validation"][
            "derived_topological_order"
        ],
        "declared_contract_and_review_derived_rows_equal": declared == derived,
        "generation_phase_node_count": len(phases),
        "independently_derived_edge_count": len(derived),
        "independently_derived_edge_root_sha256": edge_root,
        "invented_edge_count": len([row for row in declared if row not in derived]),
        "later_or_same_phase_edge_count": len(later_edges),
        "later_or_same_phase_edges": later_edges,
        "omitted_edge_count": len([row for row in derived if row not in declared]),
        "post_generation_blocked_branch_topological_sort_succeeds": topological_success,
        "reciprocal_edge_count": len(reciprocal),
        "review_topological_order": order,
        "runtime_schema_count": len(schemas),
        "schema_catalog_valid_draft_2020_12": True,
        "self_edge_count": len(self_edges),
        "unannotated_hash_bearing_field_count": len(unannotated),
        "unannotated_hash_bearing_fields": unannotated,
    }


def _tree_entries(commit: str) -> list[tuple[str, str]]:
    raw = subprocess.run(
        [
            "git",
            "ls-tree",
            "-r",
            "-z",
            "--full-tree",
            "--format=%(objectname) %(path)",
            commit,
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        check=True,
    ).stdout
    entries: list[tuple[str, str]] = []
    for encoded in raw.split(b"\0"):
        if encoded:
            oid, path = encoded.split(b" ", 1)
            entries.append((oid.decode("ascii"), path.decode("utf-8")))
    return entries


def _consumer_classification(
    path: str, raw: bytes, *, nonliteral: bool
) -> tuple[str, str, str]:
    suffix = Path(path).suffix.lower()
    runtime_signal = (
        path in NONLITERAL_READERS
        or path == "formal/python/tools/loop_control_registry_integrity.py"
        or (
            suffix == ".py"
            and any(
                marker in raw.decode("utf-8", errors="replace")
                for marker in ("read_text", "read_bytes", "json.load", "open(")
            )
        )
    )
    if nonliteral:
        category = "INDIRECT_API_CONSUMER"
    elif "/tests/" in "/" + path:
        category = "TEST_ONLY"
    elif suffix in {".lean", ".md", ".txt"}:
        category = "DOCUMENTATION_ONLY"
    elif path.startswith(("archive/", "backup/")):
        category = "HISTORICAL_ONLY"
    elif path.startswith("formal/docs/release/") and suffix == ".json":
        category = "GENERATED_REFERENCE"
    elif "integrity" in path and runtime_signal:
        category = "WRITER"
    elif runtime_signal:
        category = "DIRECT_READER"
    else:
        category = "GENERATED_REFERENCE"

    if category not in RUNTIME_REQUIRED_CATEGORIES:
        operation = "LITERAL_REFERENCE_ONLY"
    elif category == "WRITER":
        operation = "MUTATE_REGISTRY"
    elif "schema" in path.lower() or "validat" in path.lower():
        operation = "VALIDATE_ROOT_SCHEMA"
    elif "hash" in path.lower() or "integrity" in path.lower():
        operation = "COMPARE_HASH"
    else:
        operation = "READ_CURRENT_AUTHORITY"
    mechanism = (
        "REVIEWED_NONLITERAL_PATH_RULE"
        if nonliteral
        else "GIT_COMMIT_BLOB_LITERAL_OCCURRENCE"
    )
    return category, operation, mechanism


_CONSUMER_SCAN_CACHE: dict[str, list[dict[str, Any]]] = {}


def _consumer_rows(commit: str) -> list[dict[str, Any]]:
    if commit in _CONSUMER_SCAN_CACHE:
        return deepcopy(_CONSUMER_SCAN_CACHE[commit])
    baseline = _strict_json(_git_blob(SOURCE_COMMIT, BASELINE_CONSUMER_REL))
    baseline_by_path = {row["path"]: row for row in baseline["consumers"]}
    entries = _tree_entries(commit)
    tree = {path: oid for oid, path in entries}
    paths_by_oid: dict[str, list[str]] = {}
    for oid, path in entries:
        paths_by_oid.setdefault(oid, []).append(path)

    process = subprocess.Popen(
        ["git", "cat-file", "--batch"],
        cwd=REPO_ROOT,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    ordered_oids = sorted(paths_by_oid)
    batch, stderr = process.communicate(
        b"".join(oid.encode("ascii") + b"\n" for oid in ordered_oids)
    )
    if process.returncode != 0:
        raise IndependentV2ReviewError(stderr.decode("utf-8", errors="replace"))
    stream = io.BytesIO(batch)
    needle = b"LOOP_CONTROL_REGISTRY_v0.json"
    rows: list[dict[str, Any]] = []
    seen_nonliteral: set[str] = set()
    for requested_oid in ordered_oids:
        header = stream.readline().rstrip(b"\n").split(b" ")
        if len(header) != 3 or header[0].decode("ascii") != requested_oid:
            raise IndependentV2ReviewError("consumer batch stream desynchronized")
        size = int(header[2])
        raw = stream.read(size)
        if stream.read(1) != b"\n" or header[1] != b"blob":
            raise IndependentV2ReviewError("consumer batch object invalid")
        for path in paths_by_oid[requested_oid]:
            if path == REGISTRY_REL:
                continue
            findings: list[tuple[int, int, bool]] = []
            if path in NONLITERAL_READERS:
                findings.append((0, max(1, len(raw)), True))
                seen_nonliteral.add(path)
            cursor = 0
            while True:
                position = raw.find(needle, cursor)
                if position < 0:
                    break
                findings.append((position, position + len(needle), False))
                cursor = position + len(needle)
            for start, end, nonliteral in findings:
                category, operation, mechanism = _consumer_classification(
                    path, raw, nonliteral=nonliteral
                )
                if nonliteral:
                    descriptor = {
                        "git_blob": requested_oid,
                        "path": path,
                        "rule_id": "FROZEN_NONLITERAL_READERS_v2",
                        "source_sha256": sha256(raw),
                    }
                    domain = b"LOOP_CONTROL_REVIEWED_NONLITERAL_CALLSITE_v2\0"
                else:
                    descriptor = {
                        "byte_end": end,
                        "byte_start": start,
                        "git_blob": requested_oid,
                        "matched_bytes_sha256": sha256(raw[start:end]),
                        "path": path,
                    }
                    domain = b"LOOP_CONTROL_LITERAL_CALLSITE_v2\0"
                statement_hash = sha256(domain + compact_json_bytes(descriptor))
                identity = {
                    "consumer_category": category,
                    "discovery_mechanism": mechanism,
                    "operation_class": operation,
                    "repository_relative_path": path,
                    "statement_or_call_site_sha256": statement_hash,
                }
                baseline_row = baseline_by_path.get(path)
                delta = (
                    "ADDED"
                    if baseline_row is None
                    else "CHANGED"
                    if baseline_row["git_blob"] != requested_oid
                    else "UNCHANGED"
                )
                rows.append(
                    {
                        "baseline_delta_class": delta,
                        "consumer_category": category,
                        "consumer_id": "lcc2:"
                        + sha256(
                            b"LOOP_CONTROL_CONSUMER_ID_v2\0"
                            + compact_json_bytes(identity)
                        ),
                        "discovery_mechanism": mechanism,
                        "operation_class": operation,
                        "path": path,
                        "runtime_required": category in RUNTIME_REQUIRED_CATEGORIES,
                        "statement_or_call_site_sha256": statement_hash,
                    }
                )
    if seen_nonliteral != set(NONLITERAL_READERS):
        raise IndependentV2ReviewError("reviewed nonliteral consumer missing")
    rows.sort(
        key=lambda row: (
            row["path"].encode("utf-8"),
            row["statement_or_call_site_sha256"],
            row["consumer_category"],
            row["operation_class"],
            row["discovery_mechanism"],
        )
    )
    _CONSUMER_SCAN_CACHE[commit] = deepcopy(rows)
    return rows


def _consumer_summary(commit: str) -> dict[str, Any]:
    rows = _consumer_rows(commit)
    ids = [row["consumer_id"] for row in rows]
    runtime_ids = [row["consumer_id"] for row in rows if row["runtime_required"]]
    paths = {row["path"] for row in rows}
    baseline = _strict_json(_git_blob(SOURCE_COMMIT, BASELINE_CONSUMER_REL))
    baseline_paths = {row["path"] for row in baseline["consumers"]}
    return {
        "added_path_count": len(
            {row["path"] for row in rows if row["baseline_delta_class"] == "ADDED"}
        ),
        "all_identity_root_sha256": sha256(
            b"LOOP_CONTROL_INDEPENDENT_REVIEW_IDENTITIES_v2\0"
            + "\n".join(sorted(ids)).encode("utf-8")
        ),
        "contract_domain_all_identity_root_sha256": sha256(
            b"LOOP_CONTROL_ALL_CONSUMER_IDENTITIES_v2\0"
            + "\n".join(sorted(ids)).encode("utf-8")
        ),
        "baseline_changed_path_count": len(
            {row["path"] for row in rows if row["baseline_delta_class"] == "CHANGED"}
        ),
        "callsite_identity_count": len(rows),
        "nonruntime_count": len(rows) - len(runtime_ids),
        "removed_path_count": len(baseline_paths - paths),
        "runtime_required_count": len(runtime_ids),
        "runtime_required_root_sha256": sha256(
            b"LOOP_CONTROL_INDEPENDENT_REVIEW_RUNTIME_IDENTITIES_v2\0"
            + "\n".join(sorted(runtime_ids)).encode("utf-8")
        ),
        "contract_domain_runtime_required_root_sha256": sha256(
            b"LOOP_CONTROL_RUNTIME_REQUIRED_IDENTITIES_v2\0"
            + "\n".join(sorted(runtime_ids)).encode("utf-8")
        ),
        "scan_commit": commit,
        "unique_path_count": len(paths),
    }


def _consumer_review(contract: dict[str, Any]) -> dict[str, Any]:
    source_rows = _consumer_rows(SOURCE_COMMIT)
    preparation_rows = _consumer_rows(PREPARATION_COMMIT)
    source_paths = {row["path"] for row in source_rows}
    preparation_paths = {row["path"] for row in preparation_rows}
    source_ids = {row["consumer_id"] for row in source_rows}
    preparation_ids = {row["consumer_id"] for row in preparation_rows}
    frozen = contract["consumer_inventory_historical_evidence"][
        "v2_preparation_callsite_scan"
    ]
    algorithm = contract["consumer_inventory_algorithm"]
    allowed_mechanisms = set(algorithm["discovery_mechanisms"])
    schema_allowed_mechanisms = set(
        contract["runtime_schemas"]["preflight_consumer_inventory"]
        ["properties"]["consumers"]["items"]["properties"]
        ["discovery_mechanism"]["enum"]
    )
    emitted_mechanisms = {
        row["discovery_mechanism"] for row in preparation_rows
    }
    source_summary = _consumer_summary(SOURCE_COMMIT)
    preparation_summary = _consumer_summary(PREPARATION_COMMIT)
    return {
        "contract_discovery_mechanisms": sorted(allowed_mechanisms),
        "contract_discovery_pass_order": algorithm["discovery_pass_order"],
        "contract_requires_python_ast_passes": any(
            "PYTHON_AST" in value for value in algorithm["discovery_pass_order"]
        ),
        "contract_frozen_source_commit": contract["source_commit"],
        "contract_historical_callsite_count": frozen["consumer_identity_count"],
        "contract_historical_scan_is_marked_non_normative": frozen[
            "evidence_only_not_future_expectation"
        ],
        "emitted_discovery_mechanisms": sorted(emitted_mechanisms),
        "emitted_row_count_with_schema_forbidden_mechanism": sum(
            row["discovery_mechanism"] not in schema_allowed_mechanisms
            for row in preparation_rows
        ),
        "emitted_mechanisms_are_allowed_by_contract": (
            emitted_mechanisms <= allowed_mechanisms
        ),
        "legacy_literal_preparation_commit_scan": preparation_summary,
        "legacy_literal_source_commit_scan": source_summary,
        "preparation_only_identity_count": len(preparation_ids - source_ids),
        "source_only_identity_count": len(source_ids - preparation_ids),
        "preparation_only_consumer_paths": sorted(preparation_paths - source_paths),
        "review_commit_equals_contract_model_source_commit": (
            PREPARATION_COMMIT == contract["source_commit"]
        ),
        "source_witness_identity_root_matches_frozen_evidence": (
            source_summary["contract_domain_all_identity_root_sha256"]
            == frozen["identity_root_sha256"]
        ),
        "review_scanner_contract_conformant": (
            emitted_mechanisms <= allowed_mechanisms
            and emitted_mechanisms <= schema_allowed_mechanisms
        ),
        "schema_discovery_mechanisms": sorted(schema_allowed_mechanisms),
        "review_conclusion": (
            "B_BLOCKED_EXECUTABLE_LITERAL_SCANNER_DOES_NOT_IMPLEMENT_THE_"
            "FROZEN_MULTI_PASS_INVENTORY_ALGORITHM_OR_SCHEMA_MECHANISMS"
        ),
    }


def _implementation_review(contract: dict[str, Any]) -> dict[str, Any]:
    evidence = []
    markers = (
        b"--contract-v2",
        b"EXECUTION_PREFLIGHT_ATTESTATION",
        b"LOOP_CONTROL_CONSUMER_DISCOVERY_CALLSITE_v2",
        b"20260712_v2",
    )
    for relative in AUTHORIZED_IMPLEMENTATION_PATHS:
        source_raw = _git_blob(SOURCE_COMMIT, relative)
        preparation_raw = _git_blob(PREPARATION_COMMIT, relative)
        evidence.append(
            {
                "git_blob": _git_oid(PREPARATION_COMMIT, relative),
                "path": relative,
                "source_and_preparation_bytes_equal": source_raw == preparation_raw,
                "v2_marker_count": sum(marker in preparation_raw for marker in markers),
            }
        )
    orchestrator = _git_blob(
        PREPARATION_COMMIT, AUTHORIZED_IMPLEMENTATION_PATHS[0]
    )
    actual_generation_order: list[dict[str, Any]] = []
    modeled_generation_order = contract["lifecycle_contract"]["COMPLETE"][
        "generation_ledger"
    ]
    declared_edges = contract["reviewed_schema_hash_edge_table"]["rows"]
    return {
        "actual_production_v2_generation_order": actual_generation_order,
        "authorized_implementation_path_count": len(evidence),
        "authorized_implementation_paths": evidence,
        "blocked_v0_contract_binding_still_present": (
            b"CONTRACT_BUNDLE_20260711_v0.json" in orchestrator
        ),
        "blocked_v0_orchestrator_description_still_present": (
            b"blocked-v0 orchestrator" in orchestrator
        ),
        "contract_modeled_generation_order": modeled_generation_order,
        "preparation_generator_is_in_authorized_implementation_set": (
            GENERATOR_REL in AUTHORIZED_IMPLEMENTATION_PATHS
        ),
        "production_contract_v2_cli_available": b"--contract-v2" in orchestrator,
        "production_v2_execution_implementation_exists": any(
            row["v2_marker_count"] for row in evidence
        ),
        "schema_graph_and_generation_phase_table_agree": all(
            row["referenced_generation_ordinal"]
            < row["containing_generation_ordinal"]
            for row in declared_edges
        ),
        "schema_phase_and_actual_production_order_agree": (
            bool(actual_generation_order)
            and actual_generation_order == modeled_generation_order
        ),
    }


def _inventory_probe_results() -> list[dict[str, Any]]:
    controls = [
        ("V2-NC-001", "declared_graph_differs_from_schema_graph", "V2-E-DECLARED-SCHEMA-GRAPH-MISMATCH"),
        ("V2-NC-002", "schema_graph_differs_from_generation_order", "V2-E-SCHEMA-GENERATION-ORDER-MISMATCH"),
        ("V2-NC-003", "undeclared_hash_bearing_field", "V2-E-HASH-FIELD-UNDECLARED"),
        ("V2-NC-004", "later_phase_artifact_required_too_early", "V2-E-LATER-PHASE-REFERENCE"),
        ("V2-NC-005", "consumer_map_truncated_to_one_row", "V2-E-CONSUMER-INVENTORY-INCOMPLETE"),
        ("V2-NC-006", "trace_truncated_to_match_consumer_map", "V2-E-RUNTIME-TRACE-INCOMPLETE"),
        ("V2-NC-007", "consumer_map_and_trace_locally_rebound", "V2-E-CONSUMER-LOCAL-REBIND"),
        ("V2-NC-008", "stale_historical_count_treated_as_current_truth", "V2-E-STALE-CONSUMER-COUNT"),
        ("V2-NC-009", "fresh_consumer_omitted", "V2-E-FRESH-CONSUMER-OMITTED"),
        ("V2-NC-010", "invented_consumer_inserted", "V2-E-CONSUMER-INVENTED"),
        ("V2-NC-011", "runtime_required_consumer_classified_nonruntime", "V2-E-RUNTIME-REQUIRED-MISCLASSIFIED"),
        ("V2-NC-012", "baseline_path_changed_without_delta_classification", "V2-E-BASELINE-CHANGE-UNCLASSIFIED"),
        ("V2-NC-013", "preflight_inventory_altered_after_source_manifest_creation", "V2-E-PREFLIGHT-INVENTORY-BINDING-MISMATCH"),
        ("V2-NC-014", "consumer_inventory_derived_from_candidate", "V2-E-CONSUMER-INVENTORY-TRUST-ROOT"),
        ("V2-NC-015", "review_trusts_execution_inventory_without_rescan", "V2-E-REVIEW-CONSUMER-RESCAN-REQUIRED"),
    ]
    baseline = {
        "candidate_rows": [
            {"baseline_delta_class": "UNCHANGED", "consumer_id": "a", "runtime_required": True},
            {"baseline_delta_class": "CHANGED", "consumer_id": "b", "runtime_required": True},
            {"baseline_delta_class": "ADDED", "consumer_id": "c", "runtime_required": False},
        ],
        "declared_graph_edges": ["B->A"],
        "expected_generation_order": ["A", "B"],
        "fresh_omission": False,
        "generation_order": ["A", "B"],
        "hash_fields_declared": True,
        "inventory_origin": "REPOSITORY_GIT_OBJECT_SCAN",
        "later_phase_reference": False,
        "local_rebinding_attack": False,
        "normative_historical_count": None,
        "preflight_inventory_root": "root-0",
        "preflight_rows": [
            {"baseline_delta_class": "UNCHANGED", "consumer_id": "a", "runtime_required": True},
            {"baseline_delta_class": "CHANGED", "consumer_id": "b", "runtime_required": True},
            {"baseline_delta_class": "ADDED", "consumer_id": "c", "runtime_required": False},
        ],
        "review_rescanned_repository": True,
        "schema_graph_edges": ["B->A"],
        "source_manifest_inventory_root": "root-0",
        "trace_rows": ["a", "b"],
    }

    def mutate(fixture: dict[str, Any], mutation: str) -> None:
        if mutation == "declared_graph_differs_from_schema_graph":
            fixture["declared_graph_edges"] = []
        elif mutation == "schema_graph_differs_from_generation_order":
            fixture["generation_order"] = ["B", "A"]
        elif mutation == "undeclared_hash_bearing_field":
            fixture["hash_fields_declared"] = False
        elif mutation == "later_phase_artifact_required_too_early":
            fixture["later_phase_reference"] = True
        elif mutation == "consumer_map_truncated_to_one_row":
            fixture["candidate_rows"] = fixture["candidate_rows"][:1]
        elif mutation == "trace_truncated_to_match_consumer_map":
            fixture["trace_rows"] = fixture["trace_rows"][:1]
        elif mutation == "consumer_map_and_trace_locally_rebound":
            fixture["candidate_rows"] = fixture["candidate_rows"][:1]
            fixture["trace_rows"] = fixture["trace_rows"][:1]
            fixture["local_rebinding_attack"] = True
        elif mutation == "stale_historical_count_treated_as_current_truth":
            fixture["normative_historical_count"] = 520
        elif mutation == "fresh_consumer_omitted":
            fixture["candidate_rows"] = fixture["candidate_rows"][:-1]
            fixture["fresh_omission"] = True
        elif mutation == "invented_consumer_inserted":
            fixture["candidate_rows"].append(
                {
                    "baseline_delta_class": "ADDED",
                    "consumer_id": "invented",
                    "runtime_required": False,
                }
            )
        elif mutation == "runtime_required_consumer_classified_nonruntime":
            fixture["candidate_rows"][0]["runtime_required"] = False
        elif mutation == "baseline_path_changed_without_delta_classification":
            fixture["candidate_rows"][1]["baseline_delta_class"] = "UNCHANGED"
        elif mutation == "preflight_inventory_altered_after_source_manifest_creation":
            fixture["preflight_inventory_root"] = "root-mutated"
        elif mutation == "consumer_inventory_derived_from_candidate":
            fixture["inventory_origin"] = "CANDIDATE_SUPPLIED"
        elif mutation == "review_trusts_execution_inventory_without_rescan":
            fixture["review_rescanned_repository"] = False
        else:
            raise IndependentV2ReviewError(f"unknown independent probe: {mutation}")

    def validate(fixture: dict[str, Any]) -> str | None:
        if fixture["declared_graph_edges"] != fixture["schema_graph_edges"]:
            return "V2-E-DECLARED-SCHEMA-GRAPH-MISMATCH"
        if fixture["generation_order"] != fixture["expected_generation_order"]:
            return "V2-E-SCHEMA-GENERATION-ORDER-MISMATCH"
        if not fixture["hash_fields_declared"]:
            return "V2-E-HASH-FIELD-UNDECLARED"
        if fixture["later_phase_reference"]:
            return "V2-E-LATER-PHASE-REFERENCE"
        if not fixture["review_rescanned_repository"]:
            return "V2-E-REVIEW-CONSUMER-RESCAN-REQUIRED"
        if fixture["inventory_origin"] != "REPOSITORY_GIT_OBJECT_SCAN":
            return "V2-E-CONSUMER-INVENTORY-TRUST-ROOT"
        if fixture["preflight_inventory_root"] != fixture["source_manifest_inventory_root"]:
            return "V2-E-PREFLIGHT-INVENTORY-BINDING-MISMATCH"
        if fixture["normative_historical_count"] is not None:
            return "V2-E-STALE-CONSUMER-COUNT"
        if fixture["local_rebinding_attack"]:
            return "V2-E-CONSUMER-LOCAL-REBIND"
        preflight = {row["consumer_id"]: row for row in fixture["preflight_rows"]}
        candidate = {row["consumer_id"]: row for row in fixture["candidate_rows"]}
        if set(candidate) - set(preflight):
            return "V2-E-CONSUMER-INVENTED"
        if set(preflight) - set(candidate):
            return (
                "V2-E-FRESH-CONSUMER-OMITTED"
                if fixture["fresh_omission"]
                else "V2-E-CONSUMER-INVENTORY-INCOMPLETE"
            )
        if any(
            candidate[consumer_id]["runtime_required"]
            != preflight[consumer_id]["runtime_required"]
            for consumer_id in preflight
        ):
            return "V2-E-RUNTIME-REQUIRED-MISCLASSIFIED"
        if any(
            candidate[consumer_id]["baseline_delta_class"]
            != preflight[consumer_id]["baseline_delta_class"]
            for consumer_id in preflight
        ):
            return "V2-E-BASELINE-CHANGE-UNCLASSIFIED"
        runtime_ids = {
            consumer_id
            for consumer_id, row in preflight.items()
            if row["runtime_required"]
        }
        if set(fixture["trace_rows"]) != runtime_ids:
            return "V2-E-RUNTIME-TRACE-INCOMPLETE"
        return None

    if validate(baseline) is not None:
        raise IndependentV2ReviewError("independent positive probe fixture is invalid")
    baseline_root = sha256(compact_json_bytes(baseline))
    results = []
    for control_id, mutation, expected in controls:
        isolated = deepcopy(baseline)
        if isolated is baseline:
            raise IndependentV2ReviewError("control fixture was not deep copied")
        mutate(isolated, mutation)
        observed = validate(isolated)
        recreated = deepcopy(baseline)
        recreated_root = sha256(compact_json_bytes(recreated))
        results.append(
            {
                "baseline_root_sha256_after": recreated_root,
                "baseline_root_sha256_before": baseline_root,
                "control_id": control_id,
                "expected_error_code": expected,
                "evidence_scope": "REVIEWER_MODEL_ONLY_NOT_FROZEN_VALIDATOR",
                "isolated_deep_copy": True,
                "mutation": mutation,
                "mutated_fixture_root_sha256": sha256(compact_json_bytes(isolated)),
                "observed_error_code": observed,
                "passed": observed == expected,
                "subsequent_controls_uncontaminated": recreated == baseline,
            }
        )
    return results


def _control_review(
    contract: dict[str, Any], detached_execution: dict[str, Any]
) -> dict[str, Any]:
    frozen = contract["stage_a_control_contract"][
        "permanent_successor_regression_results"
    ]
    model_probes = _inventory_probe_results()
    return {
        "frozen_control_count": len(frozen),
        "frozen_control_ids_unique": len({row["control_id"] for row in frozen}) == len(frozen),
        "frozen_control_result_root_sha256": contract["stage_a_control_contract"][
            "permanent_successor_regression_results_root_sha256"
        ],
        "frozen_results_all_report_isolated_clean_baselines": all(
            row["baseline_recreated"]
            and row["baseline_root_sha256_before"] == row["baseline_root_sha256_after"]
            and row["subsequent_controls_unmodified"]
            for row in frozen
        ),
        "frozen_results_all_report_intended_code": all(
            row["passed"]
            and row["expected_error_code"] == row["observed_error_code"]
            for row in frozen
        ),
        "detached_frozen_validator_control_test": detached_execution[
            "detached_control_execution"
        ],
        "reviewer_model_probe_count": len(model_probes),
        "reviewer_model_probe_results": model_probes,
        "reviewer_model_probes_are_frozen_validator_evidence": False,
        "new_v2_control_count": sum(row["control_id"].startswith("V2-NC-") for row in frozen),
        "retained_v1_control_count": sum(row["control_id"].startswith("DAG-V1-") for row in frozen),
    }


_CUSTODY_CACHE: dict[str, Any] | None = None


def _pointer_token(value: str) -> str:
    return value.replace("~", "~0").replace("/", "~1")


def _payload_kind(value: Any) -> str:
    if value is None:
        return "NULL"
    if isinstance(value, bool):
        return "BOOLEAN"
    if isinstance(value, (int, float)):
        return "NUMBER"
    if isinstance(value, str):
        return "STRING"
    if isinstance(value, list):
        return "ARRAY"
    return "OBJECT"


def _custody_review(contract: dict[str, Any]) -> dict[str, Any]:
    global _CUSTODY_CACHE
    if _CUSTODY_CACHE is not None:
        return deepcopy(_CUSTODY_CACHE)
    source = _git_blob(SOURCE_COMMIT, REGISTRY_REL)
    registry = json.loads(source.decode("utf-8"))
    source_blob = _git_oid(SOURCE_COMMIT, REGISTRY_REL)
    entries: list[tuple[str, str, str, Any]] = []
    for key, payload in registry.items():
        if key != "workstreams":
            entries.append(("ROOT_FIELD", key, f"/{_pointer_token(key)}", payload))
    for index, payload in enumerate(registry["workstreams"]):
        logical_key = str(
            payload.get("workstream_id")
            or payload.get("id")
            or payload.get("target")
            or f"anonymous_workstream_{index}"
        )
        entries.append(("WORKSTREAM", logical_key, f"/workstreams/{index}", payload))

    occurrences: dict[tuple[str, str, str], int] = {}
    records: list[tuple[str, str, str, int, str, bytes, str]] = []
    identity_rows: list[str] = []
    pointers: list[str] = []
    for record_class, logical_key, pointer, payload in entries:
        payload_raw = compact_json_bytes(payload)
        payload_sha = sha256(payload_raw)
        occurrence_key = (record_class, logical_key, payload_sha)
        ordinal = occurrences.get(occurrence_key, 0)
        occurrences[occurrence_key] = ordinal + 1
        preimage = {
            "domain": "LOOP_CONTROL_RECORD_ID_v1",
            "identical_occurrence_ordinal": ordinal,
            "logical_key": logical_key,
            "original_json_pointer": pointer,
            "payload_sha256": payload_sha,
            "record_class": record_class,
            "source_git_blob": source_blob,
            "source_path": REGISTRY_REL,
        }
        record_id = "lcr1:" + sha256(compact_json_bytes(preimage))
        records.append(
            (
                record_id,
                record_class,
                logical_key,
                ordinal,
                pointer,
                payload_raw,
                payload_sha,
            )
        )
        identity_rows.append(f"{record_id}:{payload_sha}:{pointer}")
        pointers.append(pointer)
    records.sort(key=lambda row: row[0].encode("utf-8"))
    record_ids = [row[0] for row in records]

    history_schema = contract["runtime_schemas"]["history_index"]
    accounting = history_schema["properties"]["record_accounting"]["properties"]
    expected_roots = {
        "full": accounting["full_record_identity_root_sha256"]["const"],
        "identity_payload_pointer": accounting[
            "identity_payload_pointer_root_sha256"
        ]["const"],
        "pointers": accounting["original_pointer_set_sha256"]["const"],
    }
    observed_roots = {
        "full": sha256("\n".join(record_ids).encode("utf-8")),
        "identity_payload_pointer": sha256(
            "\n".join(sorted(identity_rows)).encode("utf-8")
        ),
        "pointers": sha256("\n".join(sorted(pointers)).encode("utf-8")),
    }

    descriptors: list[dict[str, Any]] = []
    current_lines: list[bytes] = []
    current_ids: list[str] = []
    current_size = 0

    def finish_shard() -> None:
        nonlocal current_lines, current_ids, current_size
        index = len(descriptors)
        raw = b"".join(current_lines)
        path = f"history/shards/LOOP_CONTROL_HISTORY_{index:04d}.jsonl"
        descriptor = {
            "first_record_id": current_ids[0],
            "last_record_id": current_ids[-1],
            "path": path,
            "record_count": len(current_ids),
            "record_id_root_sha256": sha256("\n".join(current_ids).encode("utf-8")),
            "sequence_index": index,
            "sha256": sha256(raw),
            "uncompressed_size_bytes": len(raw),
        }
        descriptor["shard_id"] = "lcs1:" + sha256(
            compact_json_bytes(
                {
                    "domain": "LOOP_CONTROL_SHARD_ID_v1",
                    **descriptor,
                }
            )
        )
        descriptors.append(descriptor)
        current_lines = []
        current_ids = []
        current_size = 0

    for record_id, record_class, logical_key, ordinal, pointer, payload_raw, payload_sha in records:
        record = {
            "identical_occurrence_ordinal": ordinal,
            "logical_key": logical_key,
            "original_json_pointer": pointer,
            "payload_canonical_json_utf8_base64": base64.b64encode(payload_raw).decode("ascii"),
            "payload_kind": _payload_kind(json.loads(payload_raw.decode("utf-8"))),
            "payload_sha256": payload_sha,
            "payload_size_bytes": len(payload_raw),
            "record_class": record_class,
            "record_id": record_id,
            "record_version": 1,
            "schema_id": "LOOP_CONTROL_HISTORY_RECORD_v1",
            "source_git_blob": source_blob,
            "source_path": REGISTRY_REL,
        }
        line = compact_json_bytes(record) + b"\n"
        if current_lines and current_size + len(line) > 5_242_880:
            finish_shard()
        current_lines.append(line)
        current_ids.append(record_id)
        current_size += len(line)
    if current_lines:
        finish_shard()

    compressed = gzip.compress(source, compresslevel=9, mtime=0)
    compressed = compressed[:9] + b"\xff" + compressed[10:]
    reconstructed = gzip.decompress(compressed)
    _CUSTODY_CACHE = {
        "all_record_ids_unique": len(record_ids) == len(set(record_ids)),
        "all_source_pointers_unique": len(pointers) == len(set(pointers)),
        "byte_exact_legacy_reconstruction": reconstructed == source,
        "compressed_custody_sha256": sha256(compressed),
        "compressed_custody_size_bytes": len(compressed),
        "decompressed_sha256": sha256(reconstructed),
        "decompressed_size_bytes": len(reconstructed),
        "expected_record_roots": expected_roots,
        "observed_record_roots": observed_roots,
        "record_count": len(records),
        "record_roots_match_schema_constants": observed_roots == expected_roots,
        "registry_sha256": sha256(source),
        "registry_size_bytes": len(source),
        "root_field_record_count": sum(row[1] == "ROOT_FIELD" for row in records),
        "shard_count": len(descriptors),
        "shard_descriptors": descriptors,
        "shard_ranges_are_contiguous_and_sorted": (
            sum(row["record_count"] for row in descriptors) == len(records)
            and all(
                descriptors[index]["last_record_id"]
                < descriptors[index + 1]["first_record_id"]
                for index in range(len(descriptors) - 1)
            )
        ),
        "workstream_record_count": sum(row[1] == "WORKSTREAM" for row in records),
    }
    return deepcopy(_CUSTODY_CACHE)


def _external_root_review(contract: dict[str, Any]) -> dict[str, Any]:
    frozen = contract["external_roots_of_trust"]["frozen_preparation_inputs"]
    mismatches = []
    for relative, identity in frozen.items():
        raw = _git_blob(SOURCE_COMMIT, relative)
        if (
            sha256(raw) != identity["sha256"]
            or len(raw) != identity["size_bytes"]
            or _git_oid(SOURCE_COMMIT, relative) != identity["git_blob"]
        ):
            mismatches.append(relative)
    schemas = contract["runtime_schemas"]
    schema_root = sha256(compact_json_bytes(schemas))
    implementation_rows = []
    for relative in AUTHORIZED_IMPLEMENTATION_PATHS:
        raw = _git_blob(SOURCE_COMMIT, relative)
        implementation_rows.append(
            {
                "git_blob": _git_oid(SOURCE_COMMIT, relative),
                "path": relative,
                "sha256": sha256(raw),
                "size_bytes": len(raw),
                "source_commit": SOURCE_COMMIT,
            }
        )
    implementation_root = sha256(
        compact_json_bytes(
            {
                "algorithm_id": "LOOP_CONTROL_AUTHORIZED_IMPLEMENTATION_SET_v2",
                "implementations": implementation_rows,
            }
        )
    )
    roots = contract["external_roots_of_trust"]
    symbolic = roots["lifecycle_model_symbolic_future_roots"]
    return {
        "candidate_may_rebind_expected_values": roots[
            "candidate_may_supply_or_rebind_expected_values"
        ],
        "frozen_input_count": len(frozen),
        "frozen_input_mismatches": mismatches,
        "implementation_inventory_root_matches": implementation_root
        == roots["authorized_implementation_inventory_sha256"],
        "independent_schema_catalog_root_sha256": schema_root,
        "protocol_registry_schema_and_implementation_source_roots_verify": (
            not mismatches
            and schema_root == roots["reviewed_embedded_v2_schema_catalog_root_sha256"]
            and implementation_root == roots["authorized_implementation_inventory_sha256"]
            and roots["source_registry_sha256"] == REGISTRY_SHA256
        ),
        "production_future_contract_and_review_root_resolver_implemented": False,
        "symbolic_contract_root": symbolic["accepted_v2_contract_sha256"],
        "symbolic_review_root": symbolic["accepted_v2_independent_review_sha256"],
        "symbolic_roots_explicitly_model_only": symbolic[
            "model_only_not_future_execution_expectations"
        ],
    }


_DETACHED_EXECUTION_CACHE: dict[str, Any] | None = None


def _git_revision(revision: str) -> str:
    return subprocess.run(
        ["git", "rev-parse", revision],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=True,
    ).stdout.strip()


def _run_detached_generator(
    worktree: Path, *, python_hash_seed: str, timezone: str
) -> dict[str, Any]:
    environment = os.environ.copy()
    environment.update(
        {
            "GIT_OPTIONAL_LOCKS": "0",
            "PYTHONDONTWRITEBYTECODE": "1",
            "PYTHONHASHSEED": python_hash_seed,
            "PYTHONPATH": str(worktree),
            "TZ": timezone,
        }
    )
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "formal.python.tools."
            "loop_control_registry_sharding_read_only_prototype_execution_packet_v2",
            "--write",
        ],
        cwd=worktree,
        env=environment,
        capture_output=True,
        timeout=900,
    )
    if result.returncode != 0:
        raise IndependentV2ReviewError(
            "detached v2 regeneration failed: "
            + result.stderr.decode("utf-8", errors="replace")[-2_000:]
        )
    contract_raw = (worktree / CONTRACT_REL).read_bytes()
    packet_raw = (worktree / PACKET_REL).read_bytes()
    changed = subprocess.run(
        ["git", "diff", "--name-only", "HEAD", "--"],
        cwd=worktree,
        capture_output=True,
        text=True,
        check=True,
    ).stdout.splitlines()
    regenerated_contract = _strict_json(contract_raw)
    return {
        "changed_paths": sorted(changed),
        "contract_sha256": sha256(contract_raw),
        "contract_size_bytes": len(contract_raw),
        "consumer_discovery_mechanisms": regenerated_contract[
            "consumer_inventory_algorithm"
        ]["discovery_mechanisms"],
        "consumer_discovery_pass_order": regenerated_contract[
            "consumer_inventory_algorithm"
        ]["discovery_pass_order"],
        "detached_head": _git_revision_at(worktree, "HEAD"),
        "packet_sha256": sha256(packet_raw),
        "packet_size_bytes": len(packet_raw),
        "prototype_root_created": (worktree / PROTOTYPE_REL).exists(),
        "python_hash_seed": python_hash_seed,
        "timezone": timezone,
    }


def _git_revision_at(worktree: Path, revision: str) -> str:
    return subprocess.run(
        ["git", "rev-parse", revision],
        cwd=worktree,
        capture_output=True,
        text=True,
        check=True,
    ).stdout.strip()


def _run_detached_control_test(worktree: Path) -> dict[str, Any]:
    environment = os.environ.copy()
    environment.update(
        {
            "GIT_OPTIONAL_LOCKS": "0",
            "PYTHONDONTWRITEBYTECODE": "1",
            "PYTHONHASHSEED": "31337",
            "PYTHONPATH": str(worktree),
            "TZ": "UTC",
        }
    )
    node_id = (
        TEST_REL
        + "::test_all_permanent_controls_run_from_fresh_positive_fixtures"
    )
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "pytest",
            "-q",
            "-p",
            "no:cacheprovider",
            node_id,
        ],
        cwd=worktree,
        env=environment,
        capture_output=True,
        timeout=900,
    )
    stdout = result.stdout.decode("utf-8", errors="replace")
    return {
        "detached_head": _git_revision_at(worktree, "HEAD"),
        "exact_test_node": node_id,
        "passed": result.returncode == 0 and "1 passed" in stdout,
        "prototype_root_created": (worktree / PROTOTYPE_REL).exists(),
        "return_code": result.returncode,
        "selected_test_count": 1,
    }


def _detached_execution_review() -> dict[str, Any]:
    global _DETACHED_EXECUTION_CACHE
    if _DETACHED_EXECUTION_CACHE is not None:
        return deepcopy(_DETACHED_EXECUTION_CACHE)

    temporary_roots = [
        tempfile.TemporaryDirectory(prefix=f"toe-v2-review-{index}-")
        for index in range(3)
    ]
    worktrees = [Path(root.name) / "checkout" for root in temporary_roots]
    try:
        for worktree in worktrees:
            subprocess.run(
                [
                    "git",
                    "-c",
                    "core.longpaths=true",
                    "clone",
                    "--shared",
                    "--no-checkout",
                    "--quiet",
                    str(REPO_ROOT),
                    str(worktree),
                ],
                cwd=REPO_ROOT,
                capture_output=True,
                check=True,
            )
            subprocess.run(
                ["git", "config", "core.longpaths", "true"],
                cwd=worktree,
                capture_output=True,
                check=True,
            )
            subprocess.run(
                [
                    "git",
                    "-c",
                    "core.longpaths=true",
                    "checkout",
                    "--detach",
                    "--quiet",
                    PREPARATION_COMMIT,
                ],
                cwd=worktree,
                capture_output=True,
                check=True,
            )
            clean = subprocess.run(
                ["git", "status", "--porcelain"],
                cwd=worktree,
                capture_output=True,
                text=True,
                check=True,
            ).stdout
            if clean:
                raise IndependentV2ReviewError(
                    "detached clone is not clean before regeneration"
                )
        environments = [("1", "UTC"), ("777", "America/Chicago")]
        with ThreadPoolExecutor(max_workers=2) as executor:
            futures = [
                executor.submit(
                    _run_detached_generator,
                    worktrees[index],
                    python_hash_seed=seed,
                    timezone=timezone,
                )
                for index, (seed, timezone) in enumerate(environments)
            ]
            regenerations = [future.result() for future in futures]
        control_execution = _run_detached_control_test(worktrees[2])
    finally:
        for root in temporary_roots:
            root.cleanup()

    first, second = regenerations
    regenerated_equal = all(
        first[key] == second[key]
        for key in (
            "contract_sha256",
            "contract_size_bytes",
            "packet_sha256",
            "packet_size_bytes",
        )
    )
    _DETACHED_EXECUTION_CACHE = {
        "committed_contract_sha256": CONTRACT_SHA256,
        "committed_packet_sha256": PACKET_SHA256,
        "committed_parent": _git_revision(PREPARATION_COMMIT + "^"),
        "committed_tree": _git_revision(PREPARATION_COMMIT + "^{tree}"),
        "detached_clean_checkout_commit": PREPARATION_COMMIT,
        "detached_control_execution": control_execution,
        "detached_regeneration_count": len(regenerations),
        "regenerated_contract_sha256": first["contract_sha256"],
        "regenerated_contract_size_bytes": first["contract_size_bytes"],
        "regenerated_consumer_discovery_mechanisms": first[
            "consumer_discovery_mechanisms"
        ],
        "regenerated_consumer_discovery_pass_order": first[
            "consumer_discovery_pass_order"
        ],
        "regenerated_packet_sha256": first["packet_sha256"],
        "regenerated_packet_size_bytes": first["packet_size_bytes"],
        "regeneration_runs": regenerations,
        "regenerations_byte_identical_to_each_other": regenerated_equal,
        "regenerations_equal_committed_artifacts": (
            regenerated_equal
            and first["contract_sha256"] == CONTRACT_SHA256
            and first["packet_sha256"] == PACKET_SHA256
        ),
        "review_conclusion": (
            "B_BLOCKED_FROZEN_ARTIFACTS_ARE_NOT_OUTPUTS_OF_THEIR_COMMITTED_"
            "GENERATOR"
        ),
    }
    return deepcopy(_DETACHED_EXECUTION_CACHE)


def _authority_review(packet: dict[str, Any]) -> dict[str, Any]:
    return {
        "maintenance_target": packet["maintenance_target"],
        "maintenance_target_rotated": False,
        "prototype_path_absent_at_preparation_commit": not _git_path_exists(
            PREPARATION_COMMIT, PROTOTYPE_REL
        ),
        "registry_sha256": sha256(_git_blob(PREPARATION_COMMIT, REGISTRY_REL)),
        "registry_unchanged_from_source_commit": _git_oid(
            PREPARATION_COMMIT, REGISTRY_REL
        )
        == _git_oid(SOURCE_COMMIT, REGISTRY_REL),
        "scientific_target": packet["scientific_target"],
        "scientific_target_rotated": False,
        "stage_a_executed_by_review": False,
        "stage_b_authorized": False,
        "unit_ledger_executed": False,
    }


def build_review() -> dict[str, Any]:
    packet_raw = _git_blob(PREPARATION_COMMIT, PACKET_REL)
    contract_raw = _git_blob(PREPARATION_COMMIT, CONTRACT_REL)
    if sha256(packet_raw) != PACKET_SHA256 or sha256(contract_raw) != CONTRACT_SHA256:
        raise IndependentV2ReviewError("packet or contract hash drift")
    packet = _strict_json(packet_raw)
    contract = _strict_json(contract_raw)
    if packet["contract_bundle"]["sha256"] != CONTRACT_SHA256:
        raise IndependentV2ReviewError("packet does not bind reviewed contract")
    graph = _graph_review(contract)
    if not (
        graph["independently_derived_edge_count"] == 111
        and graph["unannotated_hash_bearing_field_count"] == 10
        and graph["self_edge_count"] == 0
        and graph["reciprocal_edge_count"] == 0
        and graph["later_or_same_phase_edge_count"] == 0
        and graph["complete_branch_topological_sort_succeeds"]
        and not graph["declared_contract_and_review_derived_rows_equal"]
        and graph["invented_edge_count"] == 14
        and graph["omitted_edge_count"] == 14
    ):
        raise IndependentV2ReviewError("unexpected independent schema graph result")
    implementation = _implementation_review(contract)
    consumers = _consumer_review(contract)
    custody = _custody_review(contract)
    detached_execution = _detached_execution_review()
    controls = _control_review(contract, detached_execution)
    if not (
        detached_execution["committed_tree"] == PREPARATION_TREE
        and detached_execution["committed_parent"] == SOURCE_COMMIT
        and detached_execution["detached_regeneration_count"] == 2
        and detached_execution["regenerations_byte_identical_to_each_other"]
        and not detached_execution["regenerations_equal_committed_artifacts"]
        and detached_execution["regenerated_contract_sha256"]
        == REGENERATED_CONTRACT_SHA256
        and detached_execution["regenerated_packet_sha256"]
        == REGENERATED_PACKET_SHA256
        and all(
            not row["prototype_root_created"]
            and row["detached_head"] == PREPARATION_COMMIT
            and set(row["changed_paths"]) == {CONTRACT_REL, PACKET_REL}
            for row in detached_execution["regeneration_runs"]
        )
        and controls["detached_frozen_validator_control_test"]["passed"]
        and not controls["detached_frozen_validator_control_test"][
            "prototype_root_created"
        ]
    ):
        raise IndependentV2ReviewError(
            "unexpected detached preparation execution evidence"
        )
    if not (
        custody["record_count"] == 4_691
        and custody["shard_count"] == 14
        and custody["byte_exact_legacy_reconstruction"]
    ):
        raise IndependentV2ReviewError("custody reconstruction failed")

    blocking_codes = [
        "V2-IR-BLOCK-001-DYNAMIC-CANDIDATE-EDGE-REQUIREDNESS-MISMATCH",
        "V2-IR-BLOCK-002-PREPARATION-GENERATOR-ARTIFACT-DRIFT",
        "V2-IR-BLOCK-003-INVENTORY-ALGORITHM-IMPLEMENTATION-MISMATCH",
        "V2-IR-BLOCK-004-UNDECLARED-PREFIXED-HASH-COMMITMENTS",
    ]
    return {
        "accepted_findings": {
            "annotated_schema_subgraph_is_acyclic": True,
            "committed_focused_permanent_control_test_passes": controls[
                "detached_frozen_validator_control_test"
            ]["passed"],
            "full_4691_record_14_shard_byte_custody_model_reconstructs": True,
            "source_protocol_schema_implementation_and_registry_roots_verify": True,
        },
        "authorization": {
            "authority_cutover_authorized": False,
            "consumer_migration_authorized": False,
            "implementation_change_authorized": False,
            "maintenance_target_rotation_authorized": False,
            "monolith_modification_or_retirement_authorized": False,
            "prototype_execution_authorized": False,
            "registry_migration_execution_authorized": False,
            "scientific_claim_or_blocker_movement_authorized": False,
            "scientific_target_rotation_authorized": False,
            "stage_a_authorized": False,
            "stage_b_authorized": False,
            "unit_ledger_execution_authorized": False,
            "versioned_v3_successor_required": True,
        },
        "authority_and_nonclaim_review": _authority_review(packet),
        "blocking_findings": [
            {
                "finding_id": blocking_codes[0],
                "impact": "FOURTEEN_DYNAMIC_CANDIDATE_ARTIFACT_EDGES_ARE_DECLARED_REQUIRED_BUT_THE_FROZEN_RUNTIME_SCHEMA_REQUIRES_ONLY_ONE_ENUM_MEMBER_AND_DOES_NOT_REQUIRE_EACH_ARTIFACT_TYPE",
                "required_disposition": "PRESERVE_V2_AND_PREPARE_A_VERSIONED_SUCCESSOR_WHOSE_SCHEMA_CONTAINS_CONSTRAINTS_AND_EDGE_REQUIREDNESS_AGREE_EXACTLY",
                "severity": "BLOCKING",
            },
            {
                "finding_id": blocking_codes[1],
                "impact": "TWO_CLEAN_DETACHED_REGENERATIONS_AGREE_WITH_EACH_OTHER_BUT_NOT_WITH_THE_FROZEN_PACKET_OR_CONTRACT",
                "required_disposition": "PRESERVE_V2_AND_PREPARE_A_VERSIONED_SUCCESSOR_WHOSE_FROZEN_ARTIFACTS_ARE_EXACT_OUTPUTS_OF_ITS_COMMITTED_GENERATOR",
                "severity": "BLOCKING",
            },
            {
                "finding_id": blocking_codes[2],
                "impact": "THE_FROZEN_CONTRACT_REQUIRES_SEVEN_LITERAL_AST_DYNAMIC_AND_STRUCTURED_DISCOVERY_MECHANISMS_BUT_THE_EXECUTABLE_SCANNER_AND_REVIEW_WITNESS_USE_TWO_SCHEMA_FORBIDDEN_LITERAL_OR_HARDCODED_MECHANISMS",
                "required_disposition": "SUCCESSOR_MUST_IMPLEMENT_THE_FROZEN_REPOSITORY_ROOTED_MULTI_PASS_SCANNER_AND_VALIDATE_EVERY_EMITTED_ROW_AGAINST_THE_CONSUMER_SCHEMA_WITHOUT_USING_A_HISTORICAL_COUNT_AS_CURRENT_TRUTH",
                "severity": "BLOCKING",
            },
            {
                "finding_id": blocking_codes[3],
                "impact": "TEN_LCC2_LCR1_LCS1_AND_LCT2_SHA256_DERIVED_IDENTITY_FIELDS_ARE_HASH_BEARING_BUT_HAVE_NO_REVIEWED_EDGE_ANNOTATION_SO_ONLY_AN_ANNOTATED_SUBGRAPH_CAN_BE_TOPOLOGICALLY_VALIDATED",
                "required_disposition": "SUCCESSOR_MUST_ANNOTATE_EVERY_PREFIXED_HASH_COMMITMENT_AND_DERIVE_COMPLETE_AND_BLOCKED_GRAPHS_FROM_ALL_ACTUAL_SCHEMA_FIELDS",
                "severity": "BLOCKING",
            },
        ],
        "captured_at_utc": CAPTURED_AT_UTC,
        "consumer_inventory_review": consumers,
        "contract_bundle_sha256": CONTRACT_SHA256,
        "control_review": controls,
        "custody_review": custody,
        "decision": "B_BLOCKED_REJECT_STAGE_A_V2_EXECUTION_AUTHORIZATION_REQUIRE_VERSIONED_V3_SUCCESSOR",
        "detached_clean_checkout_determinism_review": detached_execution,
        "external_root_review": _external_root_review(contract),
        "graph_review": graph,
        "implementation_and_actual_generation_order_review": implementation,
        "lifecycle_review": {
            "complete_branch_frozen_positive_model_flag": contract["lifecycle_contract"]["COMPLETE"]["positive_model_valid"],
            "complete_branch_full_graph_independently_validated": False,
            "post_generation_blocked_branch_frozen_positive_model_flag": contract["lifecycle_contract"]["POST_GENERATION_BLOCKED"]["positive_model_valid"],
            "post_generation_blocked_branch_full_graph_independently_validated": False,
            "preflight_blocked_branch_has_no_candidate_artifacts": not contract["lifecycle_contract"]["PREFLIGHT_BLOCKED"]["candidate_artifacts_created"],
            "production_complete_branch_executable": False,
            "production_post_generation_blocked_branch_executable": False,
            "production_preflight_branch_is_v2_bound": False,
            "review_accepts_abstract_models_as_execution_authority": False,
        },
        "packet_sha256": PACKET_SHA256,
        "preparation_commit": PREPARATION_COMMIT,
        "preparation_commit_parent": SOURCE_COMMIT,
        "preparation_tree": PREPARATION_TREE,
        "recommended_next_boundary": {
            "maintenance_lane_state": "PREPARED_PAUSED_AFTER_IMMUTABLE_V2_BLOCKED_REVIEW",
            "publish_preparation_and_review_commits": True,
            "resume_scientific_target_in_a_separate_guardrailed_tranche": SCIENTIFIC_TARGET,
            "stage_a_retry_before_v3_acceptance": False,
            "versioned_successor_target": SUCCESSOR_TARGET,
        },
        "review_id": "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_PACKET_INDEPENDENT_REVIEW_20260712_v2",
        "review_scope": {
            "candidate_artifacts_created": False,
            "prototype_execution_attempted": False,
            "real_stage_a_controls_executed": 0,
            "registry_migration_or_cutover_performed": False,
            "stage_b_executed": False,
            "unit_ledger_executed": False,
        },
        "reviewed_inputs": _preparation_input_evidence(),
        "schema_id": "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_PACKET_INDEPENDENT_REVIEW_20260712_v2",
        "status": "B_BLOCKED_V2_PREPARATION_PRESERVED_STAGE_A_AND_STAGE_B_UNAUTHORIZED_MAINTENANCE_MAY_PAUSE_AND_SCIENCE_MAY_RESUME_SEPARATELY",
        "validation_interpretation": (
            "focused preparation, review, authority, registry and exhaustive Lean validation passed; "
            "the combined predecessor invocation timed out, while its constituent suites subsequently passed independently; "
            "the full unbounded Python aggregate was not run; "
            "the repository is not described as universally green."
        ),
    }


def _atomic_write(path: Path, raw: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=path.parent
    )
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(raw)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    raw = canonical_json_bytes(build_review())
    if args.check:
        if not OUTPUT_PATH.exists() or OUTPUT_PATH.read_bytes() != raw:
            raise IndependentV2ReviewError("blocked v2 independent review drift")
        print(f"stage_a_v2_independent_review: B_BLOCKED sha256={sha256(raw)}")
        return 0
    _atomic_write(OUTPUT_PATH, raw)
    print(f"stage_a_v2_independent_review: wrote B_BLOCKED sha256={sha256(raw)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
