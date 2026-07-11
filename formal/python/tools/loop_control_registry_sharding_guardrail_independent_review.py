from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import io
import json
import math
import os
from pathlib import Path
import re
import subprocess
import sys
import tarfile
import tempfile
import types
from typing import Any, Callable

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
BASELINE_COMMIT = "f8c648602d18360d45c76368bfb3e3ef830f2842"
GUARDRAIL_COMMIT = "c60cebde0116fa82d6e2e67053665711207ec408"
BASELINE_REL = "formal/docs/release/TECHNICAL_DEBT_BASELINE_20260711_v0.json"
GUARDRAIL_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_AND_CURRENT_PROJECTION_GUARDRAIL_PACKET_20260711_v0.json"
)
INVENTORY_REL = "formal/docs/release/LOOP_CONTROL_REGISTRY_CONSUMER_INVENTORY_20260711_v0.json"
MAINTENANCE_AUTHORITY_REL = "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v0.json"
CURRENT_AUTHORITY_REL = "formal/docs/release/CURRENT_AUTHORITATIVE_SURFACES_v0.md"
RETIREMENTS_REL = (
    "formal/docs/release/HISTORICAL_CURRENT_MIRROR_TEST_RETIREMENTS_20260711_v0.json"
)
AXIOM_LEDGER_REL = "formal/docs/release/LEAN_AXIOM_SPEC_BACKED_LEDGER_v0.md"
SNAPSHOT_INDEX_REL = "formal/docs/release/TOOLING_SNAPSHOT_CONTENT_INDEX_20260711_v0.json"
BASELINE_TOOL_REL = "formal/python/tools/technical_debt_baseline.py"
GUARDRAIL_TOOL_REL = "formal/python/tools/loop_control_registry_sharding_guardrail.py"
INTEGRITY_TOOL_REL = "formal/python/tools/loop_control_registry_integrity.py"
LEAN_TREE_REL = "formal/toe_formal/ToeFormal"
# Split the legacy basename so this review does not become a new lexical v0
# consumer in the frozen consumer inventory that it is reviewing.
LEGACY_REGISTRY_REL = "formal/docs/release/" + "LOOP_CONTROL_" + "REGISTRY_v0.json"

BASELINE_PATH = REPO_ROOT / BASELINE_REL
GUARDRAIL_PATH = REPO_ROOT / GUARDRAIL_REL
INVENTORY_PATH = REPO_ROOT / INVENTORY_REL
MAINTENANCE_AUTHORITY_PATH = REPO_ROOT / MAINTENANCE_AUTHORITY_REL
RETIREMENTS_PATH = REPO_ROOT / RETIREMENTS_REL
AXIOM_LEDGER_PATH = REPO_ROOT / AXIOM_LEDGER_REL
SNAPSHOT_INDEX_PATH = REPO_ROOT / SNAPSHOT_INDEX_REL
LEGACY_REGISTRY_PATH = REPO_ROOT / LEGACY_REGISTRY_REL
OUTPUT_PATH = (
    REPO_ROOT
    / "formal/docs/release/LOOP_CONTROL_REGISTRY_SHARDING_AND_CURRENT_PROJECTION_GUARDRAIL_INDEPENDENT_REVIEW_20260711_v0.json"
)

SCIENTIFIC_TARGET = "execute_pillar_seam_unit_mapping_ledger_v0"
MAINTENANCE_TARGET = "prepare_loop_control_registry_sharding_and_current_projection_packet_v0"
RECOMMENDED_CORRECTIVE_TARGET = (
    "prepare_loop_control_registry_sharding_and_current_projection_guardrail_packet_v1"
)

AXIOM_RE = re.compile(r"^\s*axiom\s+([A-Za-z_][A-Za-z0-9_'.]*)\b", re.MULTILINE)
OPAQUE_RE = re.compile(r"^\s*opaque\s+([A-Za-z_][A-Za-z0-9_'.]*)\b", re.MULTILINE)


class ReviewError(ValueError):
    pass


def _strict_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ReviewError(f"duplicate exact JSON key: {key}")
        result[key] = value
    return result


def _git_blob(commit: str, relative_path: str) -> bytes:
    completed = subprocess.run(
        ["git", "show", f"{commit}:{relative_path}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
    )
    if completed.returncode != 0:
        raise ReviewError(
            f"cannot read reviewed blob {commit}:{relative_path}: "
            + completed.stderr.decode("utf-8", errors="replace")
        )
    return completed.stdout


def _git_text(commit: str, relative_path: str) -> str:
    return _git_blob(commit, relative_path).decode("utf-8", errors="strict")


def _git_json(commit: str, relative_path: str) -> dict[str, Any]:
    value = json.loads(_git_text(commit, relative_path), object_pairs_hook=_strict_object)
    if not isinstance(value, dict):
        raise ReviewError(f"expected reviewed JSON object: {commit}:{relative_path}")
    return value


def _reviewed_lean_tree_identity() -> tuple[list[tuple[str, bytes]], str]:
    completed = subprocess.run(
        ["git", "archive", "--format=tar", BASELINE_COMMIT, LEAN_TREE_REL],
        cwd=REPO_ROOT,
        capture_output=True,
        check=True,
    )
    rows: list[tuple[str, bytes]] = []
    with tarfile.open(fileobj=io.BytesIO(completed.stdout), mode="r:") as archive:
        for member in archive.getmembers():
            if not member.isfile() or not member.name.endswith(".lean"):
                continue
            handle = archive.extractfile(member)
            if handle is None:
                raise ReviewError(f"cannot read reviewed Lean member: {member.name}")
            rows.append((member.name, handle.read()))
    rows.sort(key=lambda row: row[0].casefold())
    identity = _sha256_bytes(
        b"".join(
            path.encode("utf-8") + b"\0" + _sha256_bytes(data).encode("ascii") + b"\n"
            for path, data in rows
        )
    )
    return rows, identity


def _legacy_registry_bytes(payload: dict[str, Any]) -> bytes:
    return (json.dumps(payload, indent=2, ensure_ascii=True) + "\n").encode("utf-8")


def _load_reviewed_guardrail_module() -> types.ModuleType:
    dependency_name = "formal.python.tools.loop_control_registry_integrity"
    dependency = types.ModuleType(dependency_name)
    dependency.__file__ = str(REPO_ROOT / INTEGRITY_TOOL_REL)
    dependency_source = _git_text(GUARDRAIL_COMMIT, INTEGRITY_TOOL_REL)
    exec(compile(dependency_source, dependency.__file__, "exec"), dependency.__dict__)

    module = types.ModuleType("reviewed_loop_control_registry_sharding_guardrail_c60cebde")
    module.__file__ = str(REPO_ROOT / GUARDRAIL_TOOL_REL)
    source = _git_text(GUARDRAIL_COMMIT, GUARDRAIL_TOOL_REL)
    prior_dependency = sys.modules.get(dependency_name)
    try:
        sys.modules[dependency_name] = dependency
        exec(compile(source, module.__file__, "exec"), module.__dict__)
    finally:
        if prior_dependency is None:
            del sys.modules[dependency_name]
        else:
            sys.modules[dependency_name] = prior_dependency
    return module


subject = _load_reviewed_guardrail_module()


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _baseline_stable_id(prefix: str, identity: str) -> str:
    digest = hashlib.sha256(identity.encode("utf-8")).hexdigest()[:16].upper()
    return f"{prefix}-{digest}"


def _identity_set_sha256(identities: list[str]) -> str:
    return _sha256_bytes("\n".join(sorted(identities)).encode("utf-8"))


def canonical_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(
            payload,
            indent=2,
            sort_keys=True,
            ensure_ascii=False,
            allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")


def _strip_lean_comments(text: str) -> str:
    result: list[str] = []
    index = 0
    depth = 0
    while index < len(text):
        if depth == 0 and text.startswith("--", index):
            while index < len(text) and text[index] != "\n":
                result.append(" ")
                index += 1
            continue
        if text.startswith("/-", index):
            depth += 1
            result.extend("  ")
            index += 2
            continue
        if depth > 0:
            if text.startswith("-/", index):
                depth -= 1
                result.extend("  ")
                index += 2
                continue
            result.append("\n" if text[index] == "\n" else " ")
            index += 1
            continue
        result.append(text[index])
        index += 1
    return "".join(result)


def _independent_debt_scan() -> dict[str, Any]:
    retirements = _git_json(BASELINE_COMMIT, RETIREMENTS_REL)
    retired_rows = retirements["retired_tests"]
    retired_nodeids = [str(row["nodeid"]) for row in retired_rows]

    axiom_pairs: list[tuple[str, str]] = []
    opaque_pairs: list[tuple[str, str]] = []
    lean_rows, lean_tree_sha256 = _reviewed_lean_tree_identity()
    for rel, raw in lean_rows:
        uncommented = _strip_lean_comments(raw.decode("utf-8", errors="strict"))
        axiom_pairs.extend((rel, match.group(1)) for match in AXIOM_RE.finditer(uncommented))
        opaque_pairs.extend((rel, match.group(1)) for match in OPAQUE_RE.finditer(uncommented))

    blocking_axioms = 0
    ledger_rows = 0
    for line in _git_text(BASELINE_COMMIT, AXIOM_LEDGER_REL).splitlines():
        if not line.startswith("| `"):
            continue
        cells = [cell.strip().strip("`") for cell in line.strip().strip("|").split("|")]
        if len(cells) != 7:
            raise ReviewError(f"malformed axiom-ledger row: {line}")
        ledger_rows += 1
        blocking_axioms += cells[5] == "yes"

    snapshot = _git_json(BASELINE_COMMIT, SNAPSHOT_INDEX_REL)
    metrics = snapshot["metrics"]
    baseline = _git_json(BASELINE_COMMIT, BASELINE_REL)["technical_debt_baselines"]
    empty_sha = _sha256_bytes(b"")
    return {
        "axiom_count": len(axiom_pairs),
        "axiom_file_count": len({path for path, _ in axiom_pairs}),
        "axiom_baseline_stable_identity_set_sha256": _identity_set_sha256(
            [_baseline_stable_id("AXIOM", f"{path}::{name}") for path, name in axiom_pairs]
        ),
        "axiom_identity_set_sha256": _sha256_bytes(
            "\n".join(sorted(f"{path}::{name}" for path, name in axiom_pairs)).encode()
        ),
        "blocking_axiom_count": blocking_axioms,
        "empty_axiom_statement_line_hash_count": sum(
            row["statement_line_sha256"] == empty_sha
            for row in baseline["lean_axioms"]["axioms"]
        ),
        "ledger_axiom_row_count": ledger_rows,
        "reviewed_lean_file_count": len(lean_rows),
        "reviewed_lean_tree_identity_sha256": lean_tree_sha256,
        "opaque_candidate_count": len(opaque_pairs),
        "opaque_candidate_file_count": len({path for path, _ in opaque_pairs}),
        "opaque_baseline_stable_identity_set_sha256": _identity_set_sha256(
            [_baseline_stable_id("OPAQUE", f"{path}::{name}") for path, name in opaque_pairs]
        ),
        "empty_opaque_statement_line_hash_count": sum(
            row["statement_line_sha256"] == empty_sha
            for row in baseline["lean_opaque_definitions"]["candidates"]
        ),
        "opaque_identity_set_sha256": _sha256_bytes(
            "\n".join(sorted(f"{path}::{name}" for path, name in opaque_pairs)).encode()
        ),
        "retired_assertion_count": len(retired_rows),
        "retired_assertion_unique_nodeid_count": len(set(retired_nodeids)),
        "retired_assertion_baseline_stable_identity_set_sha256": _identity_set_sha256(
            [_baseline_stable_id("QASSERT", nodeid) for nodeid in retired_nodeids]
        ),
        "snapshot_duplicate_group_count": metrics["duplicate_group_count"],
        "snapshot_path_count": metrics["tracked_snapshot_path_count"],
        "snapshot_redundant_worktree_bytes": metrics["redundant_worktree_bytes"],
    }


def _walk_nonfinite(value: Any, path: str, found: list[str]) -> None:
    if isinstance(value, float) and not math.isfinite(value):
        found.append(path)
    elif isinstance(value, dict):
        for key, child in value.items():
            _walk_nonfinite(child, f"{path}/{key}", found)
    elif isinstance(value, list):
        for index, child in enumerate(value):
            _walk_nonfinite(child, f"{path}/{index}", found)


def _independent_registry_accounting() -> dict[str, Any]:
    raw = _git_blob(GUARDRAIL_COMMIT, LEGACY_REGISTRY_REL)
    registry = json.loads(raw.decode("utf-8"), object_pairs_hook=_strict_object)
    direct_reconstruction: dict[str, Any] = {}
    record_ids: list[str] = []
    encoded_records: list[bytes] = []
    nested_workstream_objects: list[str] = []

    def walk(value: Any, pointer: str) -> None:
        if isinstance(value, dict):
            if (
                pointer
                and "workstream_id" in value
                and not re.fullmatch(r"/workstreams/\d+", pointer)
            ):
                nested_workstream_objects.append(pointer or "/")
            for key, child in value.items():
                escaped = key.replace("~", "~0").replace("/", "~1")
                walk(child, f"{pointer}/{escaped}")
        elif isinstance(value, list):
            for index, child in enumerate(value):
                walk(child, f"{pointer}/{index}")

    walk(registry, "")
    sequence = 0
    for key, value in registry.items():
        if key == "workstreams":
            direct_reconstruction[key] = []
            for index, row in enumerate(value):
                payload_hash = _sha256_bytes(subject.canonical_jsonl_line(row)[:-1])
                record_id = f"WORKSTREAM:{row['workstream_id']}@{payload_hash[:16]}"
                record_ids.append(record_id)
                encoded_records.append(
                    subject.canonical_jsonl_line(
                        {
                            "legacy_array_index": index,
                            "legacy_json_pointer": f"/workstreams/{index}",
                            "legacy_workstream_id": row["workstream_id"],
                            "payload": row,
                            "payload_sha256": payload_hash,
                            "record_id": record_id,
                            "record_kind": "legacy_workstream",
                            "schema_id": subject.RECORD_SCHEMA_ID,
                            "schema_version": 1,
                            "sequence": sequence,
                        }
                    )
                )
                direct_reconstruction[key].append(row)
                sequence += 1
        else:
            escaped = key.replace("~", "~0").replace("/", "~1")
            payload_hash = _sha256_bytes(subject.canonical_jsonl_line(value)[:-1])
            record_id = f"ROOT:{escaped}@{payload_hash[:16]}"
            record_ids.append(record_id)
            encoded_records.append(
                subject.canonical_jsonl_line(
                    {
                        "legacy_json_pointer": f"/{escaped}",
                        "payload": value,
                        "payload_sha256": payload_hash,
                        "record_id": record_id,
                        "record_kind": "legacy_root_field",
                        "schema_id": subject.RECORD_SCHEMA_ID,
                        "schema_version": 1,
                        "sequence": sequence,
                    }
                )
            )
            direct_reconstruction[key] = value
            sequence += 1

    round_trip_records = [
        json.loads(line, object_pairs_hook=_strict_object) for line in encoded_records
    ]
    round_trip_reconstruction: dict[str, Any] = {}
    for row in round_trip_records:
        if row["record_kind"] == "legacy_root_field":
            key = row["legacy_json_pointer"][1:].replace("~1", "/").replace("~0", "~")
            round_trip_reconstruction[key] = row["payload"]
        else:
            round_trip_reconstruction.setdefault("workstreams", []).append(row["payload"])

    direct_rebuilt = _legacy_registry_bytes(direct_reconstruction)
    round_trip_rebuilt = _legacy_registry_bytes(round_trip_reconstruction)
    first_difference = next(
        (
            index
            for index, (source_byte, rebuilt_byte) in enumerate(zip(raw, round_trip_rebuilt))
            if source_byte != rebuilt_byte
        ),
        None,
    )
    if first_difference is None and len(raw) != len(round_trip_rebuilt):
        first_difference = min(len(raw), len(round_trip_rebuilt))
    nonfinite: list[str] = []
    _walk_nonfinite(registry, "", nonfinite)
    return {
        "direct_object_reserialization_byte_identical": direct_rebuilt == raw,
        "legacy_registry_sha256": _sha256_bytes(raw),
        "nested_workstream_like_object_count_outside_catalog": len(
            nested_workstream_objects
        ),
        "nested_workstream_like_object_pointers": sorted(nested_workstream_objects),
        "nonfinite_number_count": len(nonfinite),
        "record_id_count": len(record_ids),
        "record_id_unique_count": len(set(record_ids)),
        "record_jsonl_round_trip_first_difference_offset": first_difference,
        "record_jsonl_round_trip_reconstruction_byte_identical": round_trip_rebuilt
        == raw,
        "record_jsonl_round_trip_reconstruction_semantically_equal": round_trip_reconstruction
        == registry,
        "record_jsonl_round_trip_reconstructed_size_bytes": len(round_trip_rebuilt),
        "record_jsonl_round_trip_sha256": _sha256_bytes(round_trip_rebuilt),
        "source_size_bytes": len(raw),
        "root_field_record_count": len(registry) - 1,
        "total_history_record_count": len(registry) - 1 + len(registry["workstreams"]),
        "workstream_record_count": len(registry["workstreams"]),
    }


def _reviewed_commit_literal_inventory() -> dict[str, Any]:
    token = Path(LEGACY_REGISTRY_REL).name
    completed = subprocess.run(
        ["git", "grep", "-l", token, GUARDRAIL_COMMIT, "--"],
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    if completed.returncode not in {0, 1}:
        raise ReviewError(completed.stderr)
    prefix = f"{GUARDRAIL_COMMIT}:"
    paths = sorted(
        line[len(prefix) :] if line.startswith(prefix) else line.split(":", 1)[-1]
        for line in completed.stdout.splitlines()
        if line.strip()
    )
    extensions = Counter(Path(path).suffix.lower() or "<none>" for path in paths)
    registry_rel = LEGACY_REGISTRY_REL
    external_paths = [path for path in paths if path != registry_rel]
    external_extensions = Counter(
        Path(path).suffix.lower() or "<none>" for path in external_paths
    )
    return {
        "literal_path_count_all_tracked_file_types_including_monolith": len(paths),
        "literal_path_extension_counts": dict(sorted(extensions.items())),
        "external_literal_reference_path_count": len(external_paths),
        "external_non_python_literal_reference_path_count": sum(
            count
            for extension, count in external_extensions.items()
            if extension != ".py"
        ),
        "python_literal_path_count": external_extensions.get(".py", 0),
        "reviewed_commit": GUARDRAIL_COMMIT,
    }


def _fixture_layout() -> tuple[dict[str, Any], dict[str, Any], dict[str, bytes], dict[str, Any]]:
    current = {
        "ACTIVE_LANE_v0": "scientific_target_v0",
        "CURRENT_LIVE_NEXT_TARGET_v0": "scientific_target_v0",
        "active_lane": "scientific_target_v0",
        "active_workstreams": [{"status": "active", "workstream_id": "scientific_target_v0"}],
        "authority_role": "current_scientific_projection",
        "blockers": ["blocker_a"],
        "claim_ceiling": {"level": 3},
        "current_target": "scientific_target_v0",
        "current_target_evidence": "evidence.lean",
        "current_target_kind": "bounded_execution",
        "current_target_outcome": "PREPARED",
        "current_target_report": "report.json",
        "current_target_strict_outcome": "NO_PROMOTION",
        "history_index_path": "LOOP_CONTROL_HISTORY_INDEX_v1.json",
        "maintenance_authority": {
            "current_maintenance_target": "maintenance_target_v0",
            "scientific_target_displacement": False,
        },
        "maintenance_authority_path": "CURRENT_MAINTENANCE_AUTHORITY_v0.json",
        "nonpromotion_assertions": ["no_promotion"],
        "previous_target": "previous_v0",
        "schema_id": subject.CURRENT_SCHEMA_ID,
        "schema_version": 1,
        "source_legacy_registry_sha256": "0" * 64,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
    }
    current["frozen_authority_fingerprint_sha256"] = subject.authority_fingerprint(current)
    legacy = {
        "CURRENT_LIVE_NEXT_TARGET_v0": "scientific_target_v0",
        "schema_id": "legacy_v0",
        "workstreams": [{"workstream_id": "legacy_a"}],
    }
    records: list[dict[str, Any]] = []
    sequence = 0
    for key, value in legacy.items():
        if key == "workstreams":
            for index, row in enumerate(value):
                records.append(
                    _fixture_record(
                        sequence,
                        "legacy_workstream",
                        f"/workstreams/{index}",
                        row,
                        "legacy_a",
                    )
                )
                sequence += 1
        else:
            records.append(
                _fixture_record(sequence, "legacy_root_field", f"/{key}", value, key)
            )
            sequence += 1
    shards = {
        "shards/part-0001.jsonl": b"".join(
            subject.canonical_jsonl_line(row) for row in records[:2]
        ),
        "shards/part-0002.jsonl": b"".join(
            subject.canonical_jsonl_line(row) for row in records[2:]
        ),
    }
    index = {
        "schema_id": subject.INDEX_SCHEMA_ID,
        "shards": [],
        "source_legacy_canonical_sha256": _sha256_bytes(_legacy_registry_bytes(legacy)),
        "source_legacy_top_level_keys": list(legacy),
    }
    _refresh_index(index, shards)
    return current, index, shards, legacy


def _fixture_record(
    sequence: int, kind: str, pointer: str, payload: Any, identity: str
) -> dict[str, Any]:
    row = {
        "legacy_json_pointer": pointer,
        "payload": payload,
        "payload_sha256": _sha256_bytes(subject.canonical_jsonl_line(payload)[:-1]),
        "record_id": subject._stable_record_id(kind.upper(), identity, payload),
        "record_kind": kind,
        "schema_id": subject.RECORD_SCHEMA_ID,
        "schema_version": 1,
        "sequence": sequence,
    }
    if kind == "legacy_workstream":
        row["legacy_array_index"] = int(pointer.rsplit("/", 1)[1])
        row["legacy_workstream_id"] = payload["workstream_id"]
    return row


def _refresh_index(index: dict[str, Any], shards: dict[str, bytes]) -> None:
    rows: list[dict[str, Any]] = []
    for ordinal, path in enumerate(sorted(shards), start=1):
        records = [json.loads(line) for line in shards[path].splitlines()]
        rows.append(
            {
                "first_record_id": records[0]["record_id"],
                "first_sequence": records[0]["sequence"],
                "last_record_id": records[-1]["record_id"],
                "last_sequence": records[-1]["sequence"],
                "path": path,
                "record_count": len(records),
                "schema_version": 1,
                "sha256": _sha256_bytes(shards[path]),
                "shard_id": f"shard-{ordinal:04d}",
            }
        )
    index["shards"] = rows


def _rewrite_first_payload(
    index: dict[str, Any], shards: dict[str, bytes], legacy: dict[str, Any], payload: Any
) -> None:
    path = sorted(shards)[0]
    records = [json.loads(line) for line in shards[path].splitlines()]
    records[0]["payload"] = payload
    records[0]["payload_sha256"] = _sha256_bytes(subject.canonical_jsonl_line(payload)[:-1])
    shards[path] = b"".join(subject.canonical_jsonl_line(row) for row in records)
    legacy["CURRENT_LIVE_NEXT_TARGET_v0"] = payload
    _refresh_index(index, shards)
    index["source_legacy_canonical_sha256"] = _sha256_bytes(
        _legacy_registry_bytes(legacy)
    )


def _adversarial_probe_results() -> dict[str, str]:
    probes: dict[str, Callable[[dict[str, Any], dict[str, Any], dict[str, bytes], dict[str, Any]], None]] = {
        "broken_current_index_pointer": lambda current, index, shards, legacy: current.__setitem__(
            "history_index_path", "wrong-index.json"
        ),
        "authority_drift_with_rebound_fingerprint": _probe_authority_rebind,
        "duplicate_shard_id": lambda current, index, shards, legacy: index["shards"][1].__setitem__(
            "shard_id", index["shards"][0]["shard_id"]
        ),
        "noncanonical_jsonl": _probe_noncanonical_jsonl,
        "oversized_current_projection": lambda current, index, shards, legacy: current.__setitem__(
            "padding", "x" * (subject.MAX_CURRENT_PROJECTION_BYTES + 1)
        ),
        "two_maintenance_targets": lambda current, index, shards, legacy: current[
            "maintenance_authority"
        ].__setitem__("active_maintenance_targets", ["a", "b"]),
        "changed_history_with_rebound_index": lambda current, index, shards, legacy: _rewrite_first_payload(
            index, shards, legacy, "changed-target"
        ),
        "nan_history_with_rebound_index": lambda current, index, shards, legacy: _rewrite_first_payload(
            index, shards, legacy, float("nan")
        ),
    }
    results: dict[str, str] = {}
    for probe_id, mutate in probes.items():
        current, index, shards, legacy = _fixture_layout()
        mutate(current, index, shards, legacy)
        try:
            subject.validate_candidate_layout(current, index, shards)
        except Exception as exc:  # pragma: no cover - retained in artifact if fixed later
            results[probe_id] = f"REJECTED:{type(exc).__name__}:{exc}"
        else:
            results[probe_id] = "ACCEPTED_INVALID_LAYOUT"
    return results


def _probe_authority_rebind(
    current: dict[str, Any], index: dict[str, Any], shards: dict[str, bytes], legacy: dict[str, Any]
) -> None:
    current["current_target"] = "changed_scientific_target"
    current["CURRENT_LIVE_NEXT_TARGET_v0"] = "changed_scientific_target"
    current["ACTIVE_LANE_v0"] = "changed_scientific_target"
    current["active_lane"] = "changed_scientific_target"
    current["active_workstreams"][0]["workstream_id"] = "changed_scientific_target"
    current["blockers"] = []
    current["claim_ceiling"] = {"level": 5, "status": "promoted"}
    current["nonpromotion_assertions"] = []
    current["frozen_authority_fingerprint_sha256"] = subject.authority_fingerprint(
        current
    )


def _probe_noncanonical_jsonl(
    current: dict[str, Any], index: dict[str, Any], shards: dict[str, bytes], legacy: dict[str, Any]
) -> None:
    for path in list(shards):
        records = [json.loads(line) for line in shards[path].splitlines()]
        shards[path] = b"".join(
            (json.dumps(row, sort_keys=False, separators=(", ", ": ")) + "\n").encode()
            for row in records
        )
    _refresh_index(index, shards)


def _reviewed_blob_row(commit: str, relative_path: str, role: str) -> dict[str, Any]:
    raw = _git_blob(commit, relative_path)
    return {
        "path": relative_path,
        "review_source": "immutable_git_blob",
        "reviewed_blob_sha256": _sha256_bytes(raw),
        "reviewed_commit": commit,
        "role": role,
        "working_copy_state_not_used_for_regeneration": True,
    }


def _comparison(expected: dict[str, Any], observed: dict[str, Any]) -> dict[str, Any]:
    mismatches = {
        key: {"expected": expected[key], "observed": observed.get(key)}
        for key in expected
        if observed.get(key) != expected[key]
    }
    return {
        "expected": expected,
        "matches": not mismatches,
        "mismatches": mismatches,
        "observed": {key: observed.get(key) for key in expected},
    }


def build_review() -> dict[str, Any]:
    debt = _independent_debt_scan()
    accounting = _independent_registry_accounting()
    literals = _reviewed_commit_literal_inventory()
    probes = _adversarial_probe_results()
    packet = _git_json(GUARDRAIL_COMMIT, GUARDRAIL_REL)
    baseline = _git_json(BASELINE_COMMIT, BASELINE_REL)
    inventory = _git_json(GUARDRAIL_COMMIT, INVENTORY_REL)
    maintenance = _git_json(GUARDRAIL_COMMIT, MAINTENANCE_AUTHORITY_REL)
    registry = json.loads(
        _git_blob(GUARDRAIL_COMMIT, LEGACY_REGISTRY_REL).decode("utf-8"),
        object_pairs_hook=_strict_object,
    )
    debt_baseline = baseline["technical_debt_baselines"]
    baseline_comparison = _comparison(
        {
            "axiom_count": debt_baseline["lean_axioms"]["axiom_count"],
            "axiom_file_count": debt_baseline["lean_axioms"]["axiom_file_count"],
            "axiom_stable_identity_set_sha256": debt_baseline["lean_axioms"][
                "stable_identity_set_sha256"
            ],
            "blocking_axiom_count": debt_baseline["lean_axioms"][
                "blocking_full_pillar_target_count"
            ],
            "opaque_candidate_count": debt_baseline["lean_opaque_definitions"][
                "candidate_count"
            ],
            "opaque_candidate_file_count": debt_baseline["lean_opaque_definitions"][
                "candidate_file_count"
            ],
            "opaque_stable_identity_set_sha256": debt_baseline[
                "lean_opaque_definitions"
            ]["stable_identity_set_sha256"],
            "retired_assertion_count": debt_baseline["quarantined_assertions"][
                "assertion_count"
            ],
            "retired_assertion_stable_identity_set_sha256": debt_baseline[
                "quarantined_assertions"
            ]["stable_identity_set_sha256"],
            "snapshot_duplicate_group_count": debt_baseline["tooling_snapshots"][
                "duplicate_group_count"
            ],
            "snapshot_path_count": debt_baseline["tooling_snapshots"][
                "tracked_snapshot_path_count"
            ],
            "snapshot_redundant_worktree_bytes": debt_baseline["tooling_snapshots"][
                "redundant_worktree_bytes"
            ],
        },
        {
            **debt,
            "axiom_stable_identity_set_sha256": debt[
                "axiom_baseline_stable_identity_set_sha256"
            ],
            "opaque_stable_identity_set_sha256": debt[
                "opaque_baseline_stable_identity_set_sha256"
            ],
            "retired_assertion_stable_identity_set_sha256": debt[
                "retired_assertion_baseline_stable_identity_set_sha256"
            ],
        },
    )
    accounting_comparison = _comparison(
        {
            "root_field_record_count": packet["record_accounting_contract"][
                "legacy_root_field_record_count"
            ],
            "total_history_record_count": packet["record_accounting_contract"][
                "total_history_record_count"
            ],
            "workstream_record_count": packet["record_accounting_contract"][
                "workstream_record_count"
            ],
        },
        accounting,
    )
    authority_comparison = _comparison(
        {
            "maintenance_boundary_migration_execution_authorized": False,
            "maintenance_scientific_target": SCIENTIFIC_TARGET,
            "maintenance_target": MAINTENANCE_TARGET,
            "packet_migration_execution_authorized": False,
            "packet_scientific_target": SCIENTIFIC_TARGET,
            "packet_maintenance_target": MAINTENANCE_TARGET,
            "registry_scientific_target": SCIENTIFIC_TARGET,
        },
        {
            "maintenance_boundary_migration_execution_authorized": maintenance[
                "boundary"
            ]["migration_execution_authorized"],
            "maintenance_scientific_target": maintenance["scientific_authority"][
                "current_target"
            ],
            "maintenance_target": maintenance["current_maintenance_target"],
            "packet_migration_execution_authorized": packet["authorization"][
                "migration_execution_authorized"
            ],
            "packet_scientific_target": packet["authorization"]["scientific_target"],
            "packet_maintenance_target": packet["authorization"]["maintenance_target"],
            "registry_scientific_target": registry["current_projection_v0"][
                "current_target"
            ],
        },
    )
    literal_reference_comparison = _comparison(
        {
            "python_literal_reference_path_count": inventory["metrics"][
                "direct_consumer_count"
            ]
        },
        {"python_literal_reference_path_count": literals["python_literal_path_count"]},
    )
    custody_rel = baseline["verification_contract"]["local_preservation_custody_path"]
    baseline_source_binding_comparison = _comparison(
        {
            "axiom_ledger_sha256": _sha256_bytes(
                _git_blob(BASELINE_COMMIT, AXIOM_LEDGER_REL)
            ),
            "local_preservation_custody_sha256": _sha256_bytes(
                _git_blob(BASELINE_COMMIT, custody_rel)
            ),
            "registry_sha256": _sha256_bytes(
                _git_blob(BASELINE_COMMIT, LEGACY_REGISTRY_REL)
            ),
            "retirements_source_ledger_sha256": _sha256_bytes(
                _git_blob(BASELINE_COMMIT, RETIREMENTS_REL)
            ),
            "snapshot_inventory_sha256": _sha256_bytes(
                _git_blob(BASELINE_COMMIT, SNAPSHOT_INDEX_REL)
            ),
        },
        {
            "axiom_ledger_sha256": debt_baseline["lean_axioms"]["ledger_sha256"],
            "local_preservation_custody_sha256": baseline["verification_contract"][
                "local_preservation_custody_sha256"
            ],
            "registry_sha256": debt_baseline["loop_control_registry"]["sha256"],
            "retirements_source_ledger_sha256": debt_baseline[
                "quarantined_assertions"
            ]["source_ledger_sha256"],
            "snapshot_inventory_sha256": debt_baseline["tooling_snapshots"][
                "inventory_sha256"
            ],
        },
    )
    accepted_invalid = sorted(
        probe_id for probe_id, result in probes.items() if result == "ACCEPTED_INVALID_LAYOUT"
    )
    probe_expectations = {probe_id: "REJECT_INVALID_LAYOUT" for probe_id in sorted(probes)}

    return {
        "accepted_scope": {
            "baseline_counts_and_identity_sets": baseline_comparison["matches"],
            "baseline_embedded_source_hashes_match_reviewed_commit_blobs": baseline_source_binding_comparison[
                "matches"
            ],
            "byte_identical_direct_object_reserialization": accounting[
                "direct_object_reserialization_byte_identical"
            ],
            "byte_identical_proposed_jsonl_round_trip": accounting[
                "record_jsonl_round_trip_reconstruction_byte_identical"
            ],
            "nested_workstream_semantic_classification_complete": accounting[
                "nested_workstream_like_object_count_outside_catalog"
            ]
            == 0,
            "nonaction_and_scientific_authority_separation": authority_comparison[
                "matches"
            ],
            "python_literal_reference_path_count_reproduced": literal_reference_comparison[
                "matches"
            ],
            "current_source_stable_ids_are_unique": accounting["record_id_count"]
            == accounting["record_id_unique_count"],
            "top_level_record_arithmetic_reproduced": accounting_comparison["matches"],
        },
        "adversarial_probe_results": {
            "accepted_invalid_layout_count": len(accepted_invalid),
            "accepted_invalid_layouts": accepted_invalid,
            "changed_history_probe_scope": "demonstrates external-source rebind and stale unrecomputed record-ID acceptance",
            "fixture_contract_version": "REGISTRY_SHARDING_REVIEW_FIXTURE_v0",
            "probe_expectations": probe_expectations,
            "probe_set_sha256": _sha256_bytes(canonical_json_bytes(probe_expectations)),
            "results": probes,
            "reviewed_validator_blob_sha256": _sha256_bytes(
                _git_blob(GUARDRAIL_COMMIT, GUARDRAIL_TOOL_REL)
            ),
        },
        "boundary": {
            "baseline_or_guardrail_commits_amended": False,
            "consumer_migration_authorized": False,
            "maintenance_target_rotated": False,
            "monolith_modified_or_retired": False,
            "next_migration_execution_target_selected": False,
            "registry_migration_execution_authorized": False,
            "scientific_artifacts_modified": False,
            "scientific_target_rotated": False,
        },
        "captured_at_utc": "2026-07-11T00:00:00Z",
        "comparison_results": {
            "baseline_counts_and_identity_sets": baseline_comparison,
            "baseline_embedded_source_hashes": baseline_source_binding_comparison,
            "current_authority_and_nonauthorization": authority_comparison,
            "python_literal_reference_scope": literal_reference_comparison,
            "top_level_record_arithmetic": accounting_comparison,
        },
        "consumer_inventory_review": {
            **literals,
            "dynamic_and_cross_language_consumer_completeness_proved": False,
            "identified_nonliteral_reader_paths_missing_from_487_union": [
                "formal/python/tests/test_loop_control_registry_envelope_integrity_gate.py",
                "formal/python/tests/test_loop_control_registry_integrity_repair_custody_gate.py",
                "formal/python/tools/loop_control_registry_sharding_guardrail.py",
            ],
            "minimum_known_python_reader_union_count": 490,
            "finding": "The 467 count reproduces Python lexical reference paths, not a proven runtime-consumer set; the helper union is not a complete cross-language or dynamic-access source map.",
        },
        "findings": [
            {
                "finding_id": "REGISTRY-REVIEW-001",
                "severity": "CRITICAL",
                "status": "OPEN_CORRECTIVE_GUARDRAIL_REQUIRED",
                "finding": "Candidate validation trusts an index-rebound reconstruction hash instead of requiring the immutable external source hash; changed history is accepted when payload and index hashes are changed together.",
                "required_correction": "Pass and verify the frozen monolith byte hash and source identity independently of candidate index content.",
            },
            {
                "finding_id": "REGISTRY-REVIEW-002",
                "severity": "CRITICAL",
                "status": "OPEN_CORRECTIVE_GUARDRAIL_REQUIRED",
                "finding": "The proposed sorted compact JSONL round trip changes nested key order and does not reproduce the source bytes, while the packet requires byte-identical reconstruction; its recorded reconstruction hash was computed directly from the source object rather than through records.",
                "required_correction": "Demonstrate an actual record-to-JSONL-to-object byte round trip, freeze an order-preserving record payload representation or exact legacy serializer, and distinguish it from v1 canonical serializers.",
            },
            {
                "finding_id": "REGISTRY-REVIEW-003",
                "severity": "HIGH",
                "status": "OPEN_CORRECTIVE_GUARDRAIL_REQUIRED",
                "finding": "Strict JSONL is under-specified and under-enforced: noncanonical lines and NaN are accepted, and allow_nan=false is absent.",
                "required_correction": "Require finite numbers, allow_nan=false, strict UTF-8/LF, and raw-line equality to one canonical JSONL serializer.",
            },
            {
                "finding_id": "REGISTRY-REVIEW-004",
                "severity": "HIGH",
                "status": "OPEN_CORRECTIVE_GUARDRAIL_REQUIRED",
                "finding": "The validator accepts an oversized current projection, a broken current history-index pointer, and multiple maintenance-target metadata.",
                "required_correction": "Enforce projection bytes, exact index pointer binding, and exactly one live maintenance target separate from the one scientific target.",
            },
            {
                "finding_id": "REGISTRY-REVIEW-005",
                "severity": "HIGH",
                "status": "OPEN_CORRECTIVE_GUARDRAIL_REQUIRED",
                "finding": "Shard identity/closure controls do not independently reject duplicate shard IDs or writes against closed immutable shards, and gap/overlap controls are not independently identified.",
                "required_correction": "Freeze unique shard IDs/paths, closure metadata, immutable-write rejection, and separate range gap/overlap decisions.",
            },
            {
                "finding_id": "REGISTRY-REVIEW-006",
                "severity": "HIGH",
                "status": "OPEN_CORRECTIVE_GUARDRAIL_REQUIRED",
                "finding": "The proposed API omits separately named current-target/current-workstream/historical-record operations and does not freeze read/write separation or closed-history write denial.",
                "required_correction": "Version the complete read API and a separate write API with immutable history closure semantics.",
            },
            {
                "finding_id": "REGISTRY-REVIEW-007",
                "severity": "HIGH",
                "status": "OPEN_CORRECTIVE_GUARDRAIL_REQUIRED",
                "finding": "The 467/487 inventory is Python-scoped; the reviewed tree has additional non-Python literal references and dynamic construction/glob/schema-assumption coverage is not proved.",
                "required_correction": "Add a tracked all-language static/dynamic consumer source map with explicit active, historical-citation, generator, writer, and mirror classifications.",
            },
            {
                "finding_id": "REGISTRY-REVIEW-008",
                "severity": "HIGH",
                "status": "OPEN_CORRECTIVE_GUARDRAIL_REQUIRED",
                "finding": "Current IDs are unique for this source and independent of shard placement, but omit source-path lineage, truncate content SHA-256 to 64 bits, and cannot distinguish identical duplicate workstream rows.",
                "required_correction": "Bind record class, source path/blob, logical key, full content hash, and a deterministic identical-occurrence identity rule.",
            },
            {
                "finding_id": "REGISTRY-REVIEW-009",
                "severity": "MEDIUM",
                "status": "OPEN_VERSIONED_BASELINE_CORRECTION_REQUIRED",
                "finding": "The baseline headline counts are correct and declaration-block hashes exist, but 50 axiom and 20 opaque statement-line hashes equal the empty-string SHA-256 because the regex start can precede the declaration line.",
                "required_correction": "Correct statement-line extraction in a versioned baseline successor without amending f8c64860.",
            },
            {
                "finding_id": "REGISTRY-REVIEW-010",
                "severity": "MEDIUM",
                "status": "OPEN_CORRECTIVE_GUARDRAIL_REQUIRED",
                "finding": "Four workstream-shaped objects outside the /workstreams catalog are preserved transitively but lack explicit current-mirror, compatibility-container, or historical-record classification.",
                "required_correction": "Classify /active_workstreams/0, /current_projection_v0, /current_target_state, and /current_target_state/active_workstreams/0 in the migration contract.",
            },
            {
                "finding_id": "REGISTRY-REVIEW-011",
                "severity": "HIGH",
                "status": "OPEN_VERSIONED_BASELINE_CORRECTION_REQUIRED",
                "finding": "The baseline records the retired-assertion source ledger SHA-256 as 56e98643db2b891e7dbb73211cb88e02721308c43dd6ad3becf6584d70cc5592, but the immutable f8c64860 Git blob is 78c534f097205dcb117ad34161ecf4357a6a434a5ed02dd8bdaacb782ba58691; the baseline captured mixed-EOL worktree bytes and is not clean-checkout reproducible.",
                "required_correction": "Create a versioned baseline successor from normalized committed bytes, bind each source to its immutable Git blob, and add a clean-checkout regeneration control without amending f8c64860.",
            },
        ],
        "independent_baseline_reproduction": debt,
        "independent_registry_accounting": accounting,
        "input_artifacts": [
            _reviewed_blob_row(
                BASELINE_COMMIT, BASELINE_REL, "frozen technical-debt baseline"
            ),
            _reviewed_blob_row(
                BASELINE_COMMIT, BASELINE_TOOL_REL, "baseline generator under review"
            ),
            _reviewed_blob_row(
                BASELINE_COMMIT, RETIREMENTS_REL, "retired-assertion source ledger"
            ),
            _reviewed_blob_row(
                BASELINE_COMMIT, AXIOM_LEDGER_REL, "axiom classification source ledger"
            ),
            _reviewed_blob_row(
                BASELINE_COMMIT, SNAPSHOT_INDEX_REL, "snapshot-duplication source index"
            ),
            _reviewed_blob_row(
                BASELINE_COMMIT,
                LEGACY_REGISTRY_REL,
                "legacy registry source bound by the frozen baseline",
            ),
            _reviewed_blob_row(
                BASELINE_COMMIT,
                custody_rel,
                "local preservation custody bound by the frozen baseline",
            ),
            _reviewed_blob_row(
                GUARDRAIL_COMMIT, GUARDRAIL_REL, "registry-sharding v0 guardrail packet"
            ),
            _reviewed_blob_row(
                GUARDRAIL_COMMIT, GUARDRAIL_TOOL_REL, "reviewed validator and packet generator"
            ),
            _reviewed_blob_row(
                GUARDRAIL_COMMIT,
                INTEGRITY_TOOL_REL,
                "reviewed legacy serializer dependency",
            ),
            _reviewed_blob_row(
                GUARDRAIL_COMMIT, INVENTORY_REL, "frozen lexical/helper consumer inventory"
            ),
            _reviewed_blob_row(
                GUARDRAIL_COMMIT,
                MAINTENANCE_AUTHORITY_REL,
                "separate current maintenance authority",
            ),
            _reviewed_blob_row(
                GUARDRAIL_COMMIT,
                CURRENT_AUTHORITY_REL,
                "current scientific authority surface",
            ),
            _reviewed_blob_row(
                GUARDRAIL_COMMIT, LEGACY_REGISTRY_REL, "legacy registry source bytes"
            ),
            {
                "path": LEAN_TREE_REL,
                "review_source": "immutable_git_tree_projection",
                "reviewed_commit": BASELINE_COMMIT,
                "reviewed_file_count": debt["reviewed_lean_file_count"],
                "reviewed_tree_identity_sha256": debt[
                    "reviewed_lean_tree_identity_sha256"
                ],
                "role": "Lean declaration source tree used by independent debt rescan",
                "working_copy_state_not_used_for_regeneration": True,
            },
        ],
        "negative_control_review": {
            "current_control_count": packet["negative_control_count"],
            "missing_or_not_independently_enforced_controls": [
                "authority_change_with_rebound_candidate_fingerprint",
                "broken_current_history_index_pointer",
                "changed_historical_record_against_external_frozen_source",
                "consumer_still_reading_monolith_directly",
                "current_record_placed_in_history_only",
                "duplicate_shard_identity",
                "gapped_ranges_as_independent_decision",
                "noncanonical_jsonl",
                "nan_or_infinity",
                "overlapping_ranges_as_independent_decision",
                "oversized_current_projection",
                "two_live_maintenance_targets",
                "write_attempt_against_closed_shard",
                "wrong_or_missing_schema_version",
                "forged_or_unrecomputed_record_id",
            ],
            "review_outcome": "CONTROL_SET_NOT_COMPLETE_ENOUGH_FOR_MIGRATION_EXECUTION",
        },
        "review_decision": {
            "baseline_commit_decision": "ACCEPTED_COUNTS_AND_IDENTITY_SETS_ONLY_VERSIONED_SOURCE_BINDING_AND_STATEMENT_HASH_CORRECTION_REQUIRED",
            "guardrail_commit_decision": "ACCEPTED_AS_PREPARATION_EVIDENCE_REJECTED_AS_MIGRATION_EXECUTION_AUTHORITY",
            "maintenance_target": MAINTENANCE_TARGET,
            "maintenance_target_rotated": False,
            "recommended_corrective_target": RECOMMENDED_CORRECTIVE_TARGET,
            "recommended_corrective_target_selected": False,
            "registry_migration_execution_authorized": False,
            "scientific_target": SCIENTIFIC_TARGET,
            "scientific_target_rotated": False,
        },
        "review_target": "review_loop_control_registry_sharding_and_current_projection_guardrail_packet_v0",
        "schema_id": "LOOP_CONTROL_REGISTRY_SHARDING_AND_CURRENT_PROJECTION_GUARDRAIL_INDEPENDENT_REVIEW_20260711_v0",
        "status": "REVIEW_REJECTS_MIGRATION_EXECUTION_READINESS_VERSIONED_CORRECTIVE_GUARDRAIL_REQUIRED",
    }


def _atomic_write(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temp_name = tempfile.mkstemp(prefix=f".{path.name}.", suffix=".tmp", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temp_name, path)
    finally:
        if os.path.exists(temp_name):
            os.unlink(temp_name)


def main() -> int:
    parser = argparse.ArgumentParser(description="Build or verify the independent registry-guardrail review.")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    data = canonical_json_bytes(build_review())
    if args.check:
        if not OUTPUT_PATH.exists() or OUTPUT_PATH.read_bytes() != data:
            raise ReviewError("independent-review artifact mismatch")
        print(f"registry_sharding_independent_review: OK sha256={_sha256_bytes(data)}")
        return 0
    _atomic_write(OUTPUT_PATH, data)
    print(f"registry_sharding_independent_review: wrote {OUTPUT_PATH} sha256={_sha256_bytes(data)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
