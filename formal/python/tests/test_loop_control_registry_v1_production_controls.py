from __future__ import annotations

import ast
import hashlib
import inspect
import io
import json
import os
from pathlib import Path
import re
from typing import Any

import pytest

from formal.python.toe import loop_control_registry_v1 as registry
from formal.python.toe import loop_control_registry_v1_validator as validator
from formal.python.tools import (
    loop_control_registry_sharding_read_only_prototype_execution as execution,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
CONTRACT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_CONTRACT_"
    "BUNDLE_20260711_v0.json"
)
PACKET_REVIEW_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_PACKET_"
    "INDEPENDENT_REVIEW_20260711_v0.json"
)
SOURCE_REGISTRY_PATH = REPO_ROOT / "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
SOURCE_REGISTRY_SHA256 = (
    "eda451133e8bbfe1ba0e815b29735f874e8b33e61d7fc5085999c4ba38df0543"
)
PACKET_REVIEW_COMMIT = "d2d211c33885135d213bd9a9267901aad7ca7454"
PACKET_REVIEW_SHA256 = (
    "272e4eb60a1467c681f05ce7c161d3146cc0b2ff2b3ad6e08c98989e6a929f19"
)
STAGE_A_REPORT = "validation/LOOP_CONTROL_STAGE_A_PRECUTOVER_REPORT_v1.json"
SOURCE_MANIFEST = "manifests/LOOP_CONTROL_ARTIFACT_SOURCE_MANIFEST_v1.json"
RUN_MANIFEST = "manifests/LOOP_CONTROL_READ_ONLY_PROTOTYPE_RUN_MANIFEST_v1.json"
EXCLUDED_STAGE_B_CONTROLS = {
    "REGISTRY-V1-NC-044",
    "REGISTRY-READINESS-V1-RC-001",
}
EXPECTED_PUBLIC_READ_API = {
    "load_current_projection",
    "get_current_target",
    "get_current_maintenance_target",
    "get_current_workstream",
    "get_historical_record",
    "iter_historical_records",
    "verify_registry_integrity",
    "reconstruct_legacy_registry",
}
EXPECTED_VALIDATOR_API = {
    "strict_load_json",
    "strict_iter_jsonl",
    "resolve_artifact_source",
    "load_reviewed_trust_anchors",
    "validate_prototype_integrity",
    "validate_write_safety",
    "validate_shadow_parity",
    "validate_cutover_eligibility",
    "require_valid",
    "validate_history_record_payload_contract",
    "validate_validation_report_contract",
    "validate_control_harness_report_contract",
}


def _load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _contract() -> dict[str, Any]:
    return _load(CONTRACT_PATH)


def _runtime_schema(name: str) -> dict[str, Any]:
    return _contract()["runtime_schemas"][name]


def _stage_a_control_ids() -> tuple[list[str], list[str]]:
    schema = _runtime_schema("stage_a_precutover_report")
    primary = [
        row["properties"]["control_id"]["const"]
        for row in schema["properties"]["control_results"]["prefixItems"]
    ]
    runtime = [
        row["properties"]["control_id"]["const"]
        for row in schema["properties"]["runtime_contract_control_results"][
            "prefixItems"
        ]
    ]
    return primary, runtime


def test_read_only_api_surface_is_exact_and_has_no_write_entrypoint() -> None:
    assert EXPECTED_PUBLIC_READ_API.issubset(set(registry.__all__))
    assert not any(
        name.startswith(("write_", "save_", "update_", "delete_", "migrate_"))
        for name in registry.__all__
    )
    for name in EXPECTED_PUBLIC_READ_API:
        signature = inspect.signature(getattr(registry, name))
        assert next(iter(signature.parameters)) == "candidate_root"


def test_reader_and_validator_sources_have_no_filesystem_mutation_calls() -> None:
    prohibited = {
        "mkdir",
        "open",
        "remove",
        "rename",
        "rmdir",
        "touch",
        "unlink",
        "write_bytes",
        "write_text",
    }
    for module in (registry, validator):
        source = inspect.getsource(module)
        tree = ast.parse(source)
        mutations = {
            node.func.attr
            for node in ast.walk(tree)
            if isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr in prohibited
        }
        assert mutations == set()


def test_reader_strict_json_rejects_duplicate_nonfinite_and_noncanonical_bytes() -> None:
    with pytest.raises(registry.RegistryFormatError, match="duplicate"):
        registry._parse_json(b'{"x":1,"x":2}', artifact="duplicate")
    with pytest.raises(registry.RegistryFormatError, match="non-finite"):
        registry._parse_json(b'{"x":NaN}', artifact="nonfinite")
    with pytest.raises(registry.RegistryFormatError, match="noncanonical"):
        registry._strict_document(
            b'{"x":1}\n', artifact="noncanonical", maximum_bytes=100
        )
    assert registry._strict_document(
        b'{\n  "x": 1\n}\n', artifact="canonical", maximum_bytes=100
    ) == {"x": 1}


def test_validator_strict_json_and_jsonl_are_fail_closed() -> None:
    with pytest.raises(validator.RegistryValidationError) as duplicate:
        validator.strict_load_json(b'{"x":1,"x":2}')
    assert duplicate.value.error_code == "V1-E-JSON-KEY-DUPLICATE"
    with pytest.raises(validator.RegistryValidationError) as nonfinite:
        validator.strict_load_json(b'{"x":Infinity}')
    assert nonfinite.value.error_code == "V1-E-JSON-NONFINITE"
    with pytest.raises(validator.RegistryValidationError):
        list(validator.strict_iter_jsonl(io.BytesIO(b'{"x": 1}\n'), 100))


def test_missing_and_ambiguous_history_ids_use_distinct_exceptions(monkeypatch) -> None:
    record_id = "lcr1:" + "a" * 64
    descriptors = [
        {
            "first_record_id": "lcr1:" + "0" * 64,
            "last_record_id": "lcr1:" + "f" * 64,
            "path": "history/shards/LOOP_CONTROL_HISTORY_0000.jsonl",
        },
        {
            "first_record_id": "lcr1:" + "9" * 64,
            "last_record_id": "lcr1:" + "f" * 64,
            "path": "history/shards/LOOP_CONTROL_HISTORY_0001.jsonl",
        },
    ]
    monkeypatch.setattr(
        registry,
        "_load_projection_and_index",
        lambda candidate_root, anchors: (Path(candidate_root), {}, {"shards": descriptors}, {}),
    )
    monkeypatch.setattr(registry, "_index_shards", lambda index: descriptors)
    with pytest.raises(registry.AmbiguousRegistryRecordIdError):
        registry.get_historical_record(Path("candidate"), record_id)
    with pytest.raises(registry.RegistryRecordNotFoundError):
        registry.get_historical_record(Path("candidate"), "not-a-record-id")


def test_historical_lookup_loads_only_the_index_selected_shard(monkeypatch) -> None:
    record_id = "lcr1:" + "b" * 64
    descriptors = [
        {
            "first_record_id": "lcr1:" + "0" * 64,
            "last_record_id": "lcr1:" + "9" * 64,
            "path": "history/shards/LOOP_CONTROL_HISTORY_0000.jsonl",
        },
        {
            "first_record_id": "lcr1:" + "a" * 64,
            "last_record_id": "lcr1:" + "f" * 64,
            "path": "history/shards/LOOP_CONTROL_HISTORY_0001.jsonl",
        },
    ]
    loaded: list[str] = []
    monkeypatch.setattr(
        registry,
        "_load_projection_and_index",
        lambda candidate_root, anchors: (Path(candidate_root), {}, {"shards": descriptors}, {}),
    )
    monkeypatch.setattr(registry, "_index_shards", lambda index: descriptors)

    def load_selected(root: Path, descriptor: dict[str, Any]):
        loaded.append(descriptor["path"])
        return ([{"record_id": record_id, "payload_kind": "NULL"}], b"row\n")

    monkeypatch.setattr(registry, "_load_shard", load_selected)
    assert registry.get_historical_record(Path("candidate"), record_id)["record_id"] == record_id
    assert loaded == ["history/shards/LOOP_CONTROL_HISTORY_0001.jsonl"]


def test_validator_public_contract_is_present_and_cutover_is_unavailable() -> None:
    for name in EXPECTED_VALIDATOR_API:
        assert callable(getattr(validator, name))
    signature = inspect.signature(validator.validate_prototype_integrity)
    assert list(signature.parameters) == ["candidate_root", "anchors"]
    with pytest.raises(validator.RegistryValidationError) as blocked:
        validator.validate_cutover_eligibility(Path("candidate"), {}, {})
    assert blocked.value.error_code == "V1-E-STAGE-B-NOT-AUTHORIZED"


def test_reviewed_trust_anchors_are_loaded_from_git_not_candidate_values() -> None:
    assert _sha256(PACKET_REVIEW_PATH.read_bytes()) == PACKET_REVIEW_SHA256
    anchors = validator.load_reviewed_trust_anchors(
        PACKET_REVIEW_COMMIT, PACKET_REVIEW_SHA256
    )
    assert anchors["candidate_supplied_values_authoritative"] is False
    assert anchors["source_registry"]["sha256"] == SOURCE_REGISTRY_SHA256
    authorization = anchors["prototype_execution_authorization"]
    assert authorization["authorization_review_commit"] == PACKET_REVIEW_COMMIT
    assert authorization["bounded_stage_a_authorized"] is True
    assert authorization["stage_b_authorized"] is False


def test_stage_a_control_set_is_exactly_58_plus_18_and_excludes_stage_b() -> None:
    inherited, runtime = _stage_a_control_ids()
    assert len(inherited) == len(set(inherited)) == 58
    assert len(runtime) == len(set(runtime)) == 18
    assert not set(inherited).intersection(runtime)
    assert len(inherited) + len(runtime) == 76
    assert EXCLUDED_STAGE_B_CONTROLS.isdisjoint(inherited)
    assert EXCLUDED_STAGE_B_CONTROLS.isdisjoint(runtime)


def test_accepted_contract_has_runtime_manifest_source_manifest_sha_cycle() -> None:
    """Permanent regression: the accepted Stage-A contract cannot be finalized.

    The source manifest must inventory every other regular artifact, including
    the runtime manifest.  The runtime manifest must in turn carry the actual
    source-manifest SHA-256 and size.  Both identities are required to match
    actual bytes, producing an unsatisfiable mutual content-hash dependency.
    """

    contract = _contract()
    inventory = contract["artifact_source_and_candidate_tree_contract"]
    fixed = inventory["fixed_path_to_artifact_kind"]
    run_schema = contract["runtime_schemas"]["runtime_run_manifest"]
    source_schema = contract["runtime_schemas"]["artifact_source_manifest"]

    assert inventory["artifact_source_manifest_is_not_self_inventoried"] is True
    assert inventory["all_other_regular_run_root_artifacts_are_inventoried_exactly_once"] is True
    assert fixed[RUN_MANIFEST] == "RUNTIME_RUN_MANIFEST"
    assert "artifact_source_manifest" in run_schema["required"]
    pointer = run_schema["properties"]["artifact_source_manifest"]
    assert set(pointer["required"]) == {"path", "sha256", "size_bytes"}
    assert pointer["properties"]["path"]["type"] == "string"
    artifact_row = source_schema["properties"]["artifacts"]["items"]
    assert set(artifact_row["required"]) >= {
        "artifact_kind",
        "path",
        "sha256",
        "size_bytes",
    }
    assert "RUNTIME_RUN_MANIFEST" in artifact_row["properties"]["artifact_kind"]["enum"]
    assert "PATH_SHA256_SIZE_MATCH_ACTUAL_BYTES" in inventory["cross_document_invariants"]


def test_cycle_cannot_be_removed_by_candidate_internal_hash_rebinding() -> None:
    contract = _contract()
    inventory = contract["artifact_source_and_candidate_tree_contract"]
    validator_contract = contract["runtime_validator_contract"]
    assert inventory["candidate_provided_roots_are_recomputed_not_trusted"] is True
    assert (
        validator_contract[
            "candidate_internal_hashes_or_pass_flags_are_never_authoritative"
        ]
        is True
    )
    assert contract["validator_contract"]["candidate_expected_values_are_authoritative"] is False


def test_orchestrator_stops_before_run_root_and_invokes_exact_direct_node() -> None:
    source_before = _sha256(SOURCE_REGISTRY_PATH.read_bytes())
    result = execution.execute_stage_a()
    assert result["status"] == "BLOCKED_BEFORE_RUN_ROOT_CREATION"
    assert result["block_code"] == "STAGE_A-BLOCKED-ARTIFACT-HASH-CYCLE"
    assert result["controls_expected"] == 76
    assert result["controls_observed"] == 0
    assert result["run_root_created"] is False
    assert result["prototype_artifacts_created"] is False
    assert result["stage_b_behavior"] is False
    invocation = result["production_control_test_invocation"]
    assert invocation["test_path_and_id"] == (
        "formal/python/tests/test_loop_control_registry_v1_production_controls.py::"
        "test_direct_stage_a_control_harness"
    )
    assert invocation["direct_invocation_completed"] is True
    assert invocation["stage_a_run_root_supplied"] is False
    assert invocation["controls_observed"] == 0
    assert invocation["exit_code"] == 0
    assert re.fullmatch(r"[0-9a-f]{64}", invocation["stdout_sha256"])
    assert re.fullmatch(r"[0-9a-f]{64}", invocation["stderr_sha256"])
    assert _sha256(SOURCE_REGISTRY_PATH.read_bytes()) == source_before


def test_direct_stage_a_control_harness() -> None:
    """Mandatory direct node: fail closed while the reviewed SHA cycle exists."""

    configured = os.environ.get("TOE_REGISTRY_STAGE_A_RUN_ROOT")
    if not configured:
        pytest.skip("direct Stage-A orchestrator run root was not supplied")

    run_root = Path(configured).resolve()
    if not run_root.is_dir():
        pytest.fail(f"configured Stage-A run root does not exist: {run_root}")

    assert _sha256(SOURCE_REGISTRY_PATH.read_bytes()) == SOURCE_REGISTRY_SHA256
    report_path = run_root / STAGE_A_REPORT
    source_manifest_path = run_root / SOURCE_MANIFEST
    run_manifest_path = run_root / RUN_MANIFEST

    if report_path.exists():
        report = validator.strict_load_json(report_path.read_bytes(), "STAGE_A_REPORT")
        assert isinstance(report, dict)
        inherited = [row["control_id"] for row in report.get("control_results", [])]
        runtime = [
            row["control_id"]
            for row in report.get("runtime_contract_control_results", [])
        ]
        assert EXCLUDED_STAGE_B_CONTROLS.isdisjoint(inherited + runtime)
        assert report.get("total_controls_passed") != 76, (
            "the unsatisfiable source-manifest/runtime-manifest SHA cycle cannot "
            "produce legitimate 76-control Stage-A acceptance"
        )

    if source_manifest_path.exists() and run_manifest_path.exists():
        source = validator.strict_load_json(
            source_manifest_path.read_bytes(), "ARTIFACT_SOURCE_MANIFEST"
        )
        runtime = validator.strict_load_json(
            run_manifest_path.read_bytes(), "RUNTIME_RUN_MANIFEST"
        )
        assert isinstance(source, dict) and isinstance(runtime, dict)
        source_pointer = runtime["artifact_source_manifest"]
        runtime_rows = [
            row for row in source["artifacts"] if row["path"] == RUN_MANIFEST
        ]
        assert len(runtime_rows) == 1
        assert source_pointer["sha256"] == _sha256(source_manifest_path.read_bytes())
        assert runtime_rows[0]["sha256"] == _sha256(run_manifest_path.read_bytes())

    pytest.fail(
        "Stage A is BLOCKED: the accepted contract requires mutually dependent "
        "source-manifest and runtime-manifest content hashes; prepare a versioned "
        "successor rather than reporting 76 controls"
    )
