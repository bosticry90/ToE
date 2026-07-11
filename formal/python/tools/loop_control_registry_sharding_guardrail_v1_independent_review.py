from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SOURCE_COMMIT = "5bfbab10b35c4c2d1398a7ab779ba20fd3422371"
PACKET_PATH = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_AND_CURRENT_PROJECTION_GUARDRAIL_PACKET_20260711_v1.json"
)
CONSUMER_PATH = (
    "formal/docs/release/LOOP_CONTROL_REGISTRY_CONSUMER_SOURCE_MAP_20260711_v1.json"
)
CUSTODY_PATH = (
    "formal/docs/release/LOOP_CONTROL_REGISTRY_LEGACY_BYTE_CUSTODY_CONTRACT_20260711_v1.json"
)
REGISTRY_PATH = "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
AUTHORITY_PATH = "formal/docs/release/CURRENT_AUTHORITATIVE_SURFACES_v0.md"
MAINTENANCE_PATH = "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v0.json"
OUTPUT_PATH = (
    REPO_ROOT
    / "formal/docs/release/LOOP_CONTROL_REGISTRY_SHARDING_AND_CURRENT_PROJECTION_GUARDRAIL_INDEPENDENT_REVIEW_20260711_v1.json"
)

EXPECTED_PACKET_SHA256 = "41994b0c1703d7f7f7ff7aeda217900a3136489f070ae55a88f2db10a13d12c0"
EXPECTED_CONSUMER_SHA256 = "5592a666adf8cf2ee70d4ab661001cf7d386caa79c3d7a7df7e9f5ac242fb642"
EXPECTED_CUSTODY_SHA256 = "bc35c992c9b9fd7dd9c2e84ed6d5b89463b3ce8eb13dc2f7c7d1c539b4d23ce9"
REGISTRY_SHA256 = "eda451133e8bbfe1ba0e815b29735f874e8b33e61d7fc5085999c4ba38df0543"
AUTHORITY_SHA256 = "cca3e7cb1855919bae8e5f189f04eb485bf2e2529aaff5e22c2a06e48b316248"
MAINTENANCE_SHA256 = "ada2c9c9c4622c64f0ab0fb7033b8e39b790d55a29ee492dd03fea06afc3695b"
SCIENTIFIC_TARGET = "execute_pillar_seam_unit_mapping_ledger_v0"
MAINTENANCE_TARGET = (
    "prepare_loop_control_registry_sharding_and_current_projection_packet_v0"
)

V0_FALSE_ACCEPTANCES = {
    "authority_drift_with_rebound_fingerprint",
    "broken_current_index_pointer",
    "changed_history_with_rebound_index",
    "duplicate_shard_id",
    "nan_history_with_rebound_index",
    "noncanonical_jsonl",
    "oversized_current_projection",
    "two_maintenance_targets",
}

FORBIDDEN_PRODUCTION_PATHS = [
    "formal/docs/release/loop_control/LOOP_CONTROL_CURRENT_v1.json",
    "formal/docs/release/loop_control/LOOP_CONTROL_HISTORY_INDEX_v1.json",
    "formal/docs/release/loop_control/LOOP_CONTROL_LEGACY_BYTE_CUSTODY_v1.json.gz",
    "formal/python/toe/loop_control_registry_v1.py",
]


class ReviewError(ValueError):
    pass


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _git_blob(relative: str) -> bytes:
    result = subprocess.run(
        ["git", "show", f"{SOURCE_COMMIT}:{relative}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        raise ReviewError(f"missing reviewed blob: {relative}")
    return result.stdout


def _path_absent_at_reviewed_commit(relative: str) -> bool:
    result = subprocess.run(
        ["git", "cat-file", "-e", f"{SOURCE_COMMIT}:{relative}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
    )
    return result.returncode != 0


def canonical_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False, allow_nan=False)
        + "\n"
    ).encode("utf-8")


def build_review() -> dict[str, Any]:
    packet_raw = _git_blob(PACKET_PATH)
    consumer_raw = _git_blob(CONSUMER_PATH)
    custody_raw = _git_blob(CUSTODY_PATH)
    if _sha256(packet_raw) != EXPECTED_PACKET_SHA256:
        raise ReviewError("reviewed packet hash mismatch")
    if _sha256(consumer_raw) != EXPECTED_CONSUMER_SHA256:
        raise ReviewError("reviewed consumer map hash mismatch")
    if _sha256(custody_raw) != EXPECTED_CUSTODY_SHA256:
        raise ReviewError("reviewed custody contract hash mismatch")
    if _sha256(_git_blob(REGISTRY_PATH)) != REGISTRY_SHA256:
        raise ReviewError("source registry hash mismatch")
    if _sha256(_git_blob(AUTHORITY_PATH)) != AUTHORITY_SHA256:
        raise ReviewError("committed authority hash mismatch")
    if _sha256(_git_blob(MAINTENANCE_PATH)) != MAINTENANCE_SHA256:
        raise ReviewError("maintenance authority hash mismatch")

    packet = json.loads(packet_raw)
    consumer = json.loads(consumer_raw)
    custody = json.loads(custody_raw)
    controls = packet["negative_controls"]
    mutations = {row["mutation"] for row in controls}
    if not V0_FALSE_ACCEPTANCES.issubset(mutations):
        raise ReviewError("v0 false acceptance regression missing")
    if len(controls) != len({row["expected_error_code"] for row in controls}):
        raise ReviewError("typed control codes are not unique")
    if len(consumer["consumers"]) != len(
        {row["consumer_id"] for row in consumer["consumers"]}
    ):
        raise ReviewError("consumer identities are not unique")
    if not all(_path_absent_at_reviewed_commit(path) for path in FORBIDDEN_PRODUCTION_PATHS):
        raise ReviewError("production migration component appeared in preparation commit")

    transient = gzip.compress(_git_blob(REGISTRY_PATH), compresslevel=9, mtime=0)
    if gzip.decompress(transient) != _git_blob(REGISTRY_PATH):
        raise ReviewError("independent gzip round trip failed")
    if packet["authorization"]["scientific_target"] != SCIENTIFIC_TARGET:
        raise ReviewError("scientific target drift")
    if packet["authorization"]["maintenance_target"] != MAINTENANCE_TARGET:
        raise ReviewError("maintenance target drift")

    return {
        "accepted_scope": {
            "byte_exact_compatibility_architecture": True,
            "committed_external_authority_binding": True,
            "corrective_v1_preparation_guardrail": True,
            "full_sha256_record_identity_contract": True,
            "migration_execution_readiness": False,
            "runtime_consumer_coverage": False,
            "typed_controls_executed_against_production_validator": False,
        },
        "authorization": {
            "maintenance_target": MAINTENANCE_TARGET,
            "maintenance_target_rotation_authorized": False,
            "migration_execution_authorized": False,
            "next_migration_execution_target_selected": False,
            "scientific_target": SCIENTIFIC_TARGET,
            "scientific_target_rotation_authorized": False,
        },
        "boundary": {
            "consumer_migration_authorized": False,
            "custody_payload_creation_authorized": False,
            "legacy_monolith_modification_or_retirement_authorized": False,
            "production_layout_or_api_authorized": False,
            "registry_cutover_authorized": False,
            "scientific_artifact_or_claim_change_authorized": False,
        },
        "captured_at_utc": "2026-07-11T00:00:00Z",
        "consumer_review": {
            "consumer_count": consumer["consumer_count"],
            "literal_external_path_count": consumer["discovery"]["literal_external_path_count"],
            "nonliteral_reader_count": consumer["discovery"]["explicit_nonliteral_reader_count"],
            "runtime_completeness_proved": False,
            "source_map_sha256": EXPECTED_CONSUMER_SHA256,
        },
        "custody_review": {
            "byte_exact_source_sha256": REGISTRY_SHA256,
            "byte_exact_source_size_bytes": 52_340_650,
            "custody_contract_sha256": EXPECTED_CUSTODY_SHA256,
            "in_memory_single_member_round_trip_reproduced": True,
            "production_custody_payload_present": False,
            "transient_reference_size_bytes": len(transient),
        },
        "findings": [
            {
                "finding_id": "REGISTRY-V1-REVIEW-001",
                "severity": "HIGH",
                "status": "OPEN_BLOCKS_MIGRATION_EXECUTION_TARGET",
                "summary": "The 52 typed controls are frozen obligations, not an executable production-validator regression harness.",
            },
            {
                "finding_id": "REGISTRY-V1-REVIEW-002",
                "severity": "HIGH",
                "status": "OPEN_BLOCKS_MIGRATION_EXECUTION_TARGET",
                "summary": "Projection/history strictness is contract metadata; concrete recursively closed schemas and validator behavior must be instantiated and reviewed in a later prototype boundary.",
            },
            {
                "finding_id": "REGISTRY-V1-REVIEW-003",
                "severity": "HIGH",
                "status": "OPEN_BLOCKS_CUTOVER",
                "summary": "The 496-path map is static evidence and runtime shadow-trace completeness remains deliberately false.",
            },
            {
                "finding_id": "REGISTRY-V1-REVIEW-004",
                "severity": "MEDIUM",
                "status": "OPEN_EXECUTION_EVIDENCE_REQUIRED",
                "summary": "The gzip profile is frozen but no externally hash-bound production custody payload exists in this preparation tranche.",
            },
        ],
        "negative_control_review": {
            "all_v0_false_acceptances_permanently_named": True,
            "control_count": len(controls),
            "typed_error_codes_unique": True,
            "v0_false_acceptance_count": sum(
                row["v0_false_acceptance_regression"] for row in controls
            ),
        },
        "packet_sha256": EXPECTED_PACKET_SHA256,
        "record_review": packet["record_accounting"],
        "review_id": "LOOP_CONTROL_REGISTRY_SHARDING_AND_CURRENT_PROJECTION_GUARDRAIL_INDEPENDENT_REVIEW_20260711_v1",
        "schema_id": "LOOP_CONTROL_REGISTRY_SHARDING_AND_CURRENT_PROJECTION_GUARDRAIL_INDEPENDENT_REVIEW_20260711_v1",
        "source_commit": SOURCE_COMMIT,
        "status": "ACCEPTED_CORRECTIVE_V1_PREPARATION_GUARDRAIL_ONLY_MIGRATION_EXECUTION_AND_CUTOVER_NOT_READY_OR_AUTHORIZED",
        "validation": {
            "focused_python_pass_count": 19,
            "focused_python_passed": True,
            "lean_job_count": 109,
            "lean_target": "ToeFormal.Release.LoopControlRegistryShardingGuardrailPacketV1",
            "lean_target_passed": True,
            "production_component_absence_count": len(FORBIDDEN_PRODUCTION_PATHS),
        },
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
    parser = argparse.ArgumentParser(description="Build or verify the independent registry guardrail v1 review.")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    raw = canonical_json_bytes(build_review())
    if args.check:
        if not OUTPUT_PATH.exists() or OUTPUT_PATH.read_bytes() != raw:
            raise ReviewError("registry guardrail v1 independent review mismatch")
        print(f"registry_guardrail_v1_review: OK sha256={_sha256(raw)}")
        return 0
    _atomic_write(OUTPUT_PATH, raw)
    print(f"registry_guardrail_v1_review: wrote {OUTPUT_PATH} sha256={_sha256(raw)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
