from __future__ import annotations

import argparse
import ast
import base64
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
from typing import Any

from jsonschema import Draft202012Validator
from jsonschema.validators import validator_for

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SOURCE_COMMIT = "f9051af27988dd745bf39d28ae4d610973d5a029"

PACKET_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_20260711_v3.json"
)
SCHEMA_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_CLOSED_SCHEMA_BUNDLE_20260711_v3.json"
)
PROTOCOL_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_PROTOCOL_BUNDLE_20260711_v3.json"
)
GENERATOR_REL = (
    "formal/python/tools/"
    "loop_control_registry_sharding_execution_readiness_packet_v3.py"
)
TEST_REL = (
    "formal/python/tests/"
    "test_loop_control_registry_sharding_execution_readiness_packet_v3.py"
)
LEAN_REL = (
    "formal/toe_formal/ToeFormal/Release/"
    "LoopControlRegistryShardingExecutionReadinessPacketV3.lean"
)
CONSUMER_REL = (
    "formal/docs/release/LOOP_CONTROL_REGISTRY_CONSUMER_SOURCE_MAP_20260711_v1.json"
)
REGISTRY_REL = "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
MAINTENANCE_REL = "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v0.json"
AUTHORITY_REL = "formal/docs/release/CURRENT_AUTHORITATIVE_SURFACES_v0.md"
REQUIREMENTS_REL = "requirements.ci.lock"

OUTPUT_PATH = (
    REPO_ROOT
    / "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_"
    "INDEPENDENT_REVIEW_20260711_v3.json"
)

EXPECTED_SHA256 = {
    PACKET_REL: "90037c92d74f4ab18be82863dd240065bc5ebd312e5b8647b52f1b3a549cb216",
    SCHEMA_REL: "86289bf922d60c3320f040779a6043cdb3f2acf3d5393ce7503ef9d3375f6cde",
    PROTOCOL_REL: "ad65ceb56d3b284b3a55e433afc13745c3c574c9f2e7bf0fe367172924ea08e2",
    GENERATOR_REL: "7746a53f9df7f25b5e135e9d9571223a932b187f66ef67b0904962d5a50fa6ae",
    TEST_REL: "e75c938e83e5c5f9ee13eafdbfe24702124f2f2627b1978ca76989bfe4bdc9d1",
    LEAN_REL: "268cbf8ef7b296225f84991e96470f2c6c907454dd0041cfcdac2d7e4a2ffb45",
    CONSUMER_REL: "5592a666adf8cf2ee70d4ab661001cf7d386caa79c3d7a7df7e9f5ac242fb642",
    REGISTRY_REL: "eda451133e8bbfe1ba0e815b29735f874e8b33e61d7fc5085999c4ba38df0543",
    MAINTENANCE_REL: "ada2c9c9c4622c64f0ab0fb7033b8e39b790d55a29ee492dd03fea06afc3695b",
    AUTHORITY_REL: "cca3e7cb1855919bae8e5f189f04eb485bf2e2529aaff5e22c2a06e48b316248",
    REQUIREMENTS_REL: "79c5d6ca6995338c20fdf4c7bdb2748746cbef0e226de1c55489ddb25658b47b",
}

EXPECTED_GIT_BLOBS = {
    PACKET_REL: "9b257bee1abd276e586d0eaa557317b146420c6f",
    SCHEMA_REL: "eaf40d9fc8c6bd9364c2f016a19b3dc4f7b1d646",
    PROTOCOL_REL: "8d87fe5ddf9446296b71ace196d33b1c2e629ed5",
    GENERATOR_REL: "042cb84533892c61e739f2bb0c0c5bb3d510be80",
    TEST_REL: "4b9669e6647df94198e8669d8cb449015a51eeda",
    LEAN_REL: "38fdc030b4f546d60d38fc3e5562ef676c33750d",
    CONSUMER_REL: "9f9846ba735813c5b2b18f7a0115d88230a36600",
    REGISTRY_REL: "e6c5b3773dccd92fde9c0a8d486a56f993d6b235",
    MAINTENANCE_REL: "dca311d6abe38a872495c07f302d13ad886c0232",
    AUTHORITY_REL: "d46c5fb1966dcefc6b923776b7d94c4f5009b889",
    REQUIREMENTS_REL: "bcc393883b90739408ed14d53d57dd0b42d0c2bd",
}

SCIENTIFIC_TARGET = "execute_pillar_seam_unit_mapping_ledger_v0"
MAINTENANCE_TARGET = (
    "prepare_loop_control_registry_sharding_and_current_projection_packet_v0"
)
EXPECTED_RECORD_ID = (
    "lcr1:d75b26021e1590269867c3a4535d7069a6443f251600edd394983ad9e0c7fdcf"
)

FORBIDDEN_PATHS = [
    "formal/docs/release/loop_control/LOOP_CONTROL_CURRENT_v1.json",
    "formal/docs/release/loop_control/LOOP_CONTROL_HISTORY_INDEX_v1.json",
    "formal/docs/release/loop_control/shards",
    "formal/docs/release/loop_control/LOOP_CONTROL_LEGACY_BYTE_CUSTODY_v1.json.gz",
    "formal/python/toe/loop_control_registry_v1.py",
    "formal/python/toe/loop_control_registry_v1_validator.py",
    "formal/scratch/loop_control_registry_v1_prototype",
]


class IndependentReviewV3Error(ValueError):
    pass


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def canonical_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False, allow_nan=False)
        + "\n"
    ).encode("utf-8")


def compact_json_bytes(payload: Any) -> bytes:
    return json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")


def _git_blob(relative: str) -> bytes:
    result = subprocess.run(
        ["git", "show", f"{SOURCE_COMMIT}:{relative}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        raise IndependentReviewV3Error(f"missing reviewed blob: {relative}")
    return result.stdout


def _git_blob_oid(relative: str) -> str:
    result = subprocess.run(
        ["git", "rev-parse", f"{SOURCE_COMMIT}:{relative}"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    return result.stdout.strip()


def _strict_json(raw: bytes) -> Any:
    def pairs_hook(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        output: dict[str, Any] = {}
        for key, value in pairs:
            if key in output:
                raise IndependentReviewV3Error(f"duplicate JSON key: {key}")
            output[key] = value
        return output

    def reject_constant(value: str) -> Any:
        raise IndependentReviewV3Error(f"nonfinite JSON constant: {value}")

    return json.loads(raw, object_pairs_hook=pairs_hook, parse_constant=reject_constant)


def _assert_closed(node: Any, path: str = "$") -> None:
    if isinstance(node, dict):
        if node.get("type") == "object":
            if node.get("additionalProperties") is not False:
                raise IndependentReviewV3Error(f"open object schema: {path}")
            if set(node.get("required", [])) != set(node.get("properties", {})):
                raise IndependentReviewV3Error(f"required/property drift: {path}")
        for key, value in node.items():
            _assert_closed(value, f"{path}/{key}")
    elif isinstance(node, list):
        for index, value in enumerate(node):
            _assert_closed(value, f"{path}/{index}")


def _json_pointer_get(payload: Any, pointer: str) -> Any:
    current = payload
    if pointer == "":
        return current
    if not pointer.startswith("/"):
        raise IndependentReviewV3Error(f"invalid pointer: {pointer}")
    for raw_token in pointer[1:].split("/"):
        token = raw_token.replace("~1", "/").replace("~0", "~")
        current = current[int(token)] if isinstance(current, list) else current[token]
    return current


def _verify_inputs() -> None:
    for relative, expected_sha in EXPECTED_SHA256.items():
        raw = _git_blob(relative)
        if _sha256(raw) != expected_sha:
            raise IndependentReviewV3Error(f"reviewed SHA drift: {relative}")
        if _git_blob_oid(relative) != EXPECTED_GIT_BLOBS[relative]:
            raise IndependentReviewV3Error(f"reviewed Git blob drift: {relative}")


def _probe() -> dict[str, Any]:
    _verify_inputs()
    packet = _strict_json(_git_blob(PACKET_REL))
    bundle = _strict_json(_git_blob(SCHEMA_REL))
    protocol = _strict_json(_git_blob(PROTOCOL_REL))
    consumers = _strict_json(_git_blob(CONSUMER_REL))
    registry = _strict_json(_git_blob(REGISTRY_REL))
    maintenance = _strict_json(_git_blob(MAINTENANCE_REL))

    if packet["corrective_schema_bundle"]["sha256"] != EXPECTED_SHA256[SCHEMA_REL]:
        raise IndependentReviewV3Error("packet/schema cross-hash drift")
    if packet["corrective_protocol_bundle"]["sha256"] != EXPECTED_SHA256[PROTOCOL_REL]:
        raise IndependentReviewV3Error("packet/protocol cross-hash drift")
    if bundle["schema_count"] != 10 or len(bundle["schemas"]) != 10:
        raise IndependentReviewV3Error("schema count drift")
    for name, schema in bundle["schemas"].items():
        validator_for(schema).check_schema(schema)
        _assert_closed(schema, name)

    builder_names = {
        node.name
        for node in ast.parse(_git_blob(GENERATOR_REL)).body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
    }
    fixtures = protocol["typed_control_harness"]["positive_fixture_contracts"]
    if len(fixtures) != 5:
        raise IndependentReviewV3Error("fixture count drift")
    for fixture_id, contract in fixtures.items():
        if contract["builder_entrypoint"] not in builder_names:
            raise IndependentReviewV3Error(f"missing builder: {fixture_id}")
        payload = contract["fixture_payload"]
        schema = bundle["schemas"][contract["schema_name"]]
        if not Draft202012Validator(schema).is_valid(payload):
            raise IndependentReviewV3Error(f"invalid positive fixture: {fixture_id}")
        if _sha256(canonical_json_bytes(payload)) != contract[
            "canonical_fixture_sha256"
        ]:
            raise IndependentReviewV3Error(f"fixture hash drift: {fixture_id}")
        if contract["full_profile_baseline_executed"] is not False:
            raise IndependentReviewV3Error("preparation overclaims full-profile execution")

    history = fixtures["VALID_HISTORY_PAYLOAD_SOURCE_STRING_v3"]["fixture_payload"]
    source_payload = compact_json_bytes(registry["selected"])
    decoded = base64.b64decode(
        history["payload_canonical_json_utf8_base64"], validate=True
    )
    if decoded != source_payload or decoded != b'"no"':
        raise IndependentReviewV3Error("history fixture source mismatch")
    if base64.b64encode(decoded).decode("ascii") != history[
        "payload_canonical_json_utf8_base64"
    ]:
        raise IndependentReviewV3Error("history fixture is not canonical Base64")
    if history["record_id"] != EXPECTED_RECORD_ID:
        raise IndependentReviewV3Error("history fixture record ID mismatch")

    harness = protocol["typed_control_harness"]
    rows = harness["controls"] + harness["readiness_regressions"]
    control_map = {
        row["control_id"]: row["expected_exact_error_set"][0] for row in rows
    }
    if len(control_map) != 60 or control_map != protocol["control_error_map"]:
        raise IndependentReviewV3Error("control/error mapping drift")
    if _sha256(compact_json_bytes(control_map)) != protocol[
        "control_error_map_sha256"
    ]:
        raise IndependentReviewV3Error("control/error mapping hash drift")
    issue_schema = protocol["production_validator_interface"]["error_result"]
    issue_validator = Draft202012Validator(issue_schema)
    for control_id, error_code in control_map.items():
        issue = {
            "artifact_path": "validation/report.json",
            "control_id": control_id,
            "error_code": error_code,
            "json_pointer": "",
            "message": "independent mapping probe",
        }
        if not issue_validator.is_valid(issue):
            raise IndependentReviewV3Error(f"correct issue rejected: {control_id}")
        issue["error_code"] = "V1-E-WRONG"
        if issue_validator.is_valid(issue):
            raise IndependentReviewV3Error(f"wrong issue accepted: {control_id}")

    regressions = harness["readiness_regressions"]
    if len(regressions) != 8:
        raise IndependentReviewV3Error("readiness regression count drift")
    for index, row in enumerate(regressions, start=1):
        if row["control_sequence"] != index or len(row["mutation_matrix"]) != 1:
            raise IndependentReviewV3Error("non-atomic readiness regression")
        fixture = fixtures[row["positive_fixture_id"]]
        case = row["mutation_matrix"][0]
        if _json_pointer_get(fixture["fixture_payload"], case["json_pointer"]) != case[
            "before"
        ]:
            raise IndependentReviewV3Error(f"mutation baseline drift: {row['control_id']}")
        if row["positive_artifact_validator_args"] != fixture[
            "artifact_contract_validator_args"
        ]:
            raise IndependentReviewV3Error("artifact validator argument drift")
        if row["production_artifact_validator_implemented_or_executed"] is not False:
            raise IndependentReviewV3Error("artifact validator execution overclaim")
    rc2 = regressions[1]["mutation_matrix"][0]
    before = base64.b64decode(rc2["before"], validate=True)
    after = base64.b64decode(rc2["after"], validate=True)
    if before != after or base64.b64encode(after).decode("ascii") == rc2["after"]:
        raise IndependentReviewV3Error("RC-002 is not an exact pad-bit alias probe")
    if "ONE_VALID_ISSUE" in json.dumps(regressions) or "BASELINE_SHA256" in json.dumps(
        regressions
    ):
        raise IndependentReviewV3Error("symbolic mutation value remains")

    field_map = bundle["field_path_profile_map"]
    if len(field_map) != 33 or set(field_map.values()) - set(bundle["path_profiles"]):
        raise IndependentReviewV3Error("field semantic profile map drift")
    if _sha256(compact_json_bytes(field_map)) != bundle[
        "field_path_profile_map_contract"
    ]["mapping_sha256"]:
        raise IndependentReviewV3Error("field semantic map hash drift")
    consumer_path_schema = bundle["schemas"]["consumer_source_map"]["properties"][
        "consumers"
    ]["items"]["properties"]["path"]
    consumer_validator = Draft202012Validator(consumer_path_schema)
    if consumers["consumer_count"] != 496 or not all(
        consumer_validator.is_valid(row["path"]) for row in consumers["consumers"]
    ):
        raise IndependentReviewV3Error("consumer path coverage drift")
    shard_schema = bundle["schemas"]["history_index"]["properties"]["shards"][
        "items"
    ]["properties"]["path"]
    shard_validator = Draft202012Validator(shard_schema)
    if not shard_validator.is_valid(
        "history/shards/LOOP_CONTROL_HISTORY_0001.jsonl"
    ) or shard_validator.is_valid("other/LOOP_CONTROL_HISTORY_0001.jsonl"):
        raise IndependentReviewV3Error("shard path contract drift")

    derivation = harness["full_profile_execution_context_derivation"]
    if derivation["realized_full_profile_baselines_executed"] is not False:
        raise IndependentReviewV3Error("full-profile execution overclaim")
    if set(derivation["profile_invocations"]) != {
        "CUTOVER_ELIGIBILITY",
        "PROTOTYPE_INTEGRITY",
        "SHADOW_PARITY",
        "WRITE_SAFETY",
    }:
        raise IndependentReviewV3Error("full-profile invocation coverage drift")
    for row in regressions:
        invocation = derivation["profile_invocations"][row["validator_profile"]]
        if row["full_candidate_profile_entrypoint"] != invocation["entrypoint"]:
            raise IndependentReviewV3Error("full-profile entrypoint drift")

    if maintenance["current_maintenance_target"] != MAINTENANCE_TARGET:
        raise IndependentReviewV3Error("maintenance target drift")
    if maintenance["scientific_authority"]["current_target"] != SCIENTIFIC_TARGET:
        raise IndependentReviewV3Error("scientific target drift")
    if any(packet["boundary"].values()):
        raise IndependentReviewV3Error("packet boundary overclaim")
    if any((REPO_ROOT / relative).exists() for relative in FORBIDDEN_PATHS):
        raise IndependentReviewV3Error("forbidden production/prototype path exists")

    return {
        "closed_schema_count": 10,
        "consumer_path_count": 496,
        "control_error_pair_count": 60,
        "field_semantic_profile_mapping_count": 33,
        "full_profile_baselines_executed": False,
        "positive_fixture_count": 5,
        "readiness_regression_count": 8,
        "reviewed_input_count": len(EXPECTED_SHA256),
        "schema_profile_count": len(bundle["path_profiles"]),
        "source_backed_history_record_id": history["record_id"],
    }


def build_review() -> dict[str, Any]:
    evidence = _probe()
    return {
        "acceptance_evidence": evidence,
        "authorization": {
            "corrective_v3_preparation_accepted": True,
            "cutover_authorized": False,
            "maintenance_target": MAINTENANCE_TARGET,
            "maintenance_target_rotation_authorized": False,
            "migration_execution_authorized": False,
            "production_artifact_validators_implemented_or_executed": False,
            "prototype_selection_authorized": False,
            "registry_migration_execution_readiness_accepted": False,
            "scientific_target": SCIENTIFIC_TARGET,
            "scientific_target_rotation_authorized": False,
            "unit_ledger_execution_authorized": False,
        },
        "captured_at_utc": "2026-07-11T00:00:00Z",
        "decision": (
            "ACCEPT_CORRECTIVE_V3_AS_BOUNDED_PREPARATION_CONTRACT_ONLY_"
            "NO_PRODUCTION_EXECUTION_MIGRATION_CUTOVER_OR_AUTHORITY"
        ),
        "independent_findings": [
            {
                "finding_id": "REGISTRY-READINESS-V3-REVIEW-001",
                "status": "CLOSED_FOR_PREPARATION_CONTRACT",
                "summary": (
                    "Exact 60-row control/error binding, five executable artifact fixtures, "
                    "and eight concrete atomic regression cases reproduce without symbolic "
                    "values or source-membership drift."
                ),
            },
            {
                "finding_id": "REGISTRY-READINESS-V3-REVIEW-002",
                "status": "CLOSED_FOR_PREPARATION_CONTRACT",
                "summary": (
                    "All ten schemas are closed; the 33-field semantic map, repository and "
                    "prototype paths, RFC 6901 pointers, run IDs, and fixed shard directory "
                    "are executable and fail closed under adversarial probes."
                ),
            },
            {
                "finding_id": "REGISTRY-READINESS-V3-REVIEW-003",
                "status": "OPEN_FUTURE_IMPLEMENTATION_OBLIGATION_NOT_A_V3_DEFECT",
                "summary": (
                    "Production artifact validators, realized candidate roots and anchors, "
                    "the 60-control harness, full-profile baselines, custody reconstruction, "
                    "and runtime shadow tracing remain unimplemented and unexecuted."
                ),
            },
        ],
        "packet_sha256": EXPECTED_SHA256[PACKET_REL],
        "protocol_sha256": EXPECTED_SHA256[PROTOCOL_REL],
        "residual_obligations": [
            "IMPLEMENT_CLOSED_PRODUCTION_SCHEMAS_AND_VALIDATOR",
            "EXECUTE_52_PLUS_8_CONTROL_HARNESS_AGAINST_READ_ONLY_PROTOTYPE",
            "PROVE_BYTE_EXACT_CUSTODY_RECONSTRUCTION_IN_CLEAN_CHECKOUT",
            "CAPTURE_RUNTIME_SHADOW_PARITY_WITHOUT_CONSUMER_MIGRATION",
            "INDEPENDENTLY_REVIEW_PROTOTYPE_BEFORE_ANY_EXECUTION_SELECTION",
        ],
        "review_id": (
            "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_"
            "INDEPENDENT_REVIEW_20260711_v3"
        ),
        "reviewed_commit": SOURCE_COMMIT,
        "schema_bundle_sha256": EXPECTED_SHA256[SCHEMA_REL],
        "schema_id": (
            "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_READINESS_PACKET_"
            "INDEPENDENT_REVIEW_20260711_v3"
        ),
        "status": (
            "ACCEPTED_CORRECTIVE_V3_PREPARATION_CONTRACT_NO_PRODUCTION_"
            "VALIDATOR_HARNESS_PROTOTYPE_MIGRATION_CUTOVER_OR_AUTHORITY"
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
    parser = argparse.ArgumentParser(
        description="Build or verify the independent corrective readiness-v3 review."
    )
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    args = parser.parse_args()
    raw = canonical_json_bytes(build_review())
    if args.check:
        if not OUTPUT_PATH.exists() or OUTPUT_PATH.read_bytes() != raw:
            raise IndependentReviewV3Error("corrective readiness-v3 review drift")
        print(f"corrective_readiness_v3_review: OK sha256={_sha256(raw)}")
        return 0
    _atomic_write(OUTPUT_PATH, raw)
    print(f"corrective_readiness_v3_review: wrote sha256={_sha256(raw)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
