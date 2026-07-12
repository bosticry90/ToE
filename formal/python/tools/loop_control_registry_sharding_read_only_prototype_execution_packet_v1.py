"""Build the one-way Stage-A registry prototype execution contract v1.

This is preparation only.  It replaces the unsatisfiable reciprocal manifest
hash contract with a directed acyclic custody chain and freezes a terminal
execution envelope.  It does not modify the v0 implementation, create a
prototype run root, execute any of the 76 Stage-A controls, rotate authority,
or authorize Stage B.
"""

from __future__ import annotations

import argparse
from copy import deepcopy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
from typing import Any, Final

from jsonschema import Draft202012Validator

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT: Final = find_repo_root(Path(__file__))
SOURCE_COMMIT: Final = "04b9200fa7b5b60df4a78f27b6d6fd8905101a22"
CAPTURED_AT_UTC: Final = "2026-07-11T00:00:00Z"

PACKET_REL: Final = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_PACKET_"
    "20260711_v1.json"
)
CONTRACT_REL: Final = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_CONTRACT_"
    "BUNDLE_20260711_v1.json"
)
PACKET_PATH: Final = REPO_ROOT / PACKET_REL
CONTRACT_PATH: Final = REPO_ROOT / CONTRACT_REL

SCIENTIFIC_TARGET: Final = "execute_pillar_seam_unit_mapping_ledger_v0"
MAINTENANCE_TARGET: Final = (
    "prepare_loop_control_registry_sharding_and_current_projection_packet_v0"
)
PACKET_TARGET: Final = (
    "prepare_loop_control_registry_sharding_read_only_prototype_execution_packet_v1"
)
REVIEW_TARGET: Final = (
    "review_loop_control_registry_sharding_read_only_prototype_execution_packet_v1"
)
EXECUTION_TARGET: Final = (
    "execute_loop_control_registry_sharding_read_only_prototype_v1"
)

REGISTRY_REL: Final = "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
MAINTENANCE_AUTHORITY_REL: Final = (
    "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v0.json"
)
AUTHORITATIVE_SURFACES_REL: Final = (
    "formal/docs/release/CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
CONSUMER_MAP_REL: Final = (
    "formal/docs/release/LOOP_CONTROL_REGISTRY_CONSUMER_SOURCE_MAP_20260711_v1.json"
)
V3_SCHEMAS_REL: Final = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_CLOSED_SCHEMA_BUNDLE_20260711_v3.json"
)
V3_PROTOCOL_REL: Final = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_EXECUTION_PROTOCOL_BUNDLE_20260711_v3.json"
)
V0_PACKET_REL: Final = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_PACKET_"
    "20260711_v0.json"
)
V0_CONTRACT_REL: Final = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_CONTRACT_"
    "BUNDLE_20260711_v0.json"
)
V0_REVIEW_REL: Final = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_PACKET_"
    "INDEPENDENT_REVIEW_20260711_v0.json"
)
ORCHESTRATOR_REL: Final = (
    "formal/python/tools/"
    "loop_control_registry_sharding_read_only_prototype_execution.py"
)
READER_REL: Final = "formal/python/toe/loop_control_registry_v1.py"
VALIDATOR_REL: Final = "formal/python/toe/loop_control_registry_v1_validator.py"
PRODUCTION_TEST_REL: Final = (
    "formal/python/tests/test_loop_control_registry_v1_production_controls.py"
)
REQUIREMENTS_REL: Final = "requirements.ci.lock"

AUTHORIZED_IMPLEMENTATION_PATHS: Final = [
    ORCHESTRATOR_REL,
    READER_REL,
    VALIDATOR_REL,
    PRODUCTION_TEST_REL,
]

PRODUCTION_LAYOUT_PATHS: Final = [
    "formal/docs/release/loop_control/LOOP_CONTROL_CURRENT_v1.json",
    "formal/docs/release/loop_control/LOOP_CONTROL_HISTORY_INDEX_v1.json",
    "formal/docs/release/loop_control/shards",
    "formal/docs/release/loop_control/LOOP_CONTROL_LEGACY_BYTE_CUSTODY_v1.json.gz",
    "formal/scratch/loop_control_registry_v1_prototype",
]

# sha256, git blob, byte count at SOURCE_COMMIT.
EXPECTED_INPUTS: Final[dict[str, tuple[str, str, int]]] = {
    V0_PACKET_REL: (
        "661655d3a6ba8f77b75652f45e1709275f0c0ae372b87a18a868316502a76168",
        "a77882a8d601662411bf33ab8b93e9153eb7fe1c",
        3313,
    ),
    V0_CONTRACT_REL: (
        "272279d414591b25b3a519d22d92659f4a662ce1c9cbd5fadf3067f1eaa8f0bb",
        "abf0d597c05342a37a31db5e166dd2b5531cb888",
        392459,
    ),
    V0_REVIEW_REL: (
        "272e4eb60a1467c681f05ce7c161d3146cc0b2ff2b3ad6e08c98989e6a929f19",
        "d717c7276a26a9b35e32a1b77cb02db7cac6a8ef",
        13126,
    ),
    ORCHESTRATOR_REL: (
        "59e4c47674ad0f00ddccaf978ea420b8495c8f16d67529639ec5527cf863fae7",
        "1ad5d758f727d3f705f4977b7f02a0400ca9b8d6",
        11589,
    ),
    READER_REL: (
        "699f85df13d3023711b56be842a2124067b5620af24407aa691301ec7951380d",
        "5d0bf0c293796e6576267a128369ae84c2481191",
        34616,
    ),
    VALIDATOR_REL: (
        "149779b8c13ffda4be332f6b871f64bf88819e4c2c3b0302bbeb5e578463a3b2",
        "8d1428a5f4f92358f09b16d2b65dff6826467b02",
        82650,
    ),
    PRODUCTION_TEST_REL: (
        "fb2396bc1df11bbddd5b5e65eb74700694734ab49968d3d897d14cf779a0a6eb",
        "a664297cf8ece147b1a9783b5500fb76843174db",
        15340,
    ),
    V3_SCHEMAS_REL: (
        "86289bf922d60c3320f040779a6043cdb3f2acf3d5393ce7503ef9d3375f6cde",
        "eaf40d9fc8c6bd9364c2f016a19b3dc4f7b1d646",
        438862,
    ),
    V3_PROTOCOL_REL: (
        "ad65ceb56d3b284b3a55e433afc13745c3c574c9f2e7bf0fe367172924ea08e2",
        "8d87fe5ddf9446296b71ace196d33b1c2e629ed5",
        187789,
    ),
    REGISTRY_REL: (
        "eda451133e8bbfe1ba0e815b29735f874e8b33e61d7fc5085999c4ba38df0543",
        "e6c5b3773dccd92fde9c0a8d486a56f993d6b235",
        52340650,
    ),
    CONSUMER_MAP_REL: (
        "5592a666adf8cf2ee70d4ab661001cf7d386caa79c3d7a7df7e9f5ac242fb642",
        "9f9846ba735813c5b2b18f7a0115d88230a36600",
        469583,
    ),
    MAINTENANCE_AUTHORITY_REL: (
        "ada2c9c9c4622c64f0ab0fb7033b8e39b790d55a29ee492dd03fea06afc3695b",
        "dca311d6abe38a872495c07f302d13ad886c0232",
        1768,
    ),
    AUTHORITATIVE_SURFACES_REL: (
        "cca3e7cb1855919bae8e5f189f04eb485bf2e2529aaff5e22c2a06e48b316248",
        "d46c5fb1966dcefc6b923776b7d94c4f5009b889",
        714575,
    ),
    REQUIREMENTS_REL: (
        "79c5d6ca6995338c20fdf4c7bdb2748746cbef0e226de1c55489ddb25658b47b",
        "bcc393883b90739408ed14d53d57dd0b42d0c2bd",
        741,
    ),
}

SOURCE_REGISTRY_SHA256: Final = EXPECTED_INPUTS[REGISTRY_REL][0]
V0_CYCLE_ERROR: Final = "V1-E-UNSATISFIABLE-ARTIFACT-MANIFEST-CYCLE"
FIXED_EXECUTION_COMMAND: Final = (
    "python -m formal.python.tools."
    "loop_control_registry_sharding_read_only_prototype_execution "
    "--execute --contract-v1"
)
DIRECT_TEST_NODE: Final = (
    "formal/python/tests/test_loop_control_registry_v1_production_controls.py::"
    "test_direct_stage_a_control_harness"
)
DIRECT_TEST_COMMAND: Final = (
    "python -m pytest -q -p no:cacheprovider " + DIRECT_TEST_NODE
)

GRAPH_ORDER: Final = [
    "EXTERNAL_TRUST_ROOTS",
    "SOURCE_MANIFEST",
    "CORE_CANDIDATE_ARTIFACTS",
    "GENERATED_EVIDENCE",
    "RUNTIME_MANIFEST",
    "EXECUTION_REPORT",
    "TERMINAL_ENVELOPE",
    "POSTTERMINAL_DAG_CONTROL_RESULTS",
    "STAGE_A_INDEPENDENT_REVIEW",
]
GRAPH_BINDS: Final = {
    "EXTERNAL_TRUST_ROOTS": [],
    "SOURCE_MANIFEST": ["EXTERNAL_TRUST_ROOTS"],
    "CORE_CANDIDATE_ARTIFACTS": ["SOURCE_MANIFEST"],
    "GENERATED_EVIDENCE": ["SOURCE_MANIFEST", "CORE_CANDIDATE_ARTIFACTS"],
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

SOURCE_INPUT_ROLE_PATHS: Final = {
    "SUCCESSOR_CONTRACT": CONTRACT_REL,
    "CLOSED_SCHEMAS": V3_SCHEMAS_REL,
    "PROTOCOL": V3_PROTOCOL_REL,
    "ORCHESTRATOR": ORCHESTRATOR_REL,
    "VALIDATOR": VALIDATOR_REL,
    "READER_API": READER_REL,
    "PRODUCTION_CONTROL_TEST": PRODUCTION_TEST_REL,
    "SOURCE_REGISTRY": REGISTRY_REL,
    "CONSUMER_SOURCE_MAP": CONSUMER_MAP_REL,
    "REQUIREMENTS_LOCK": REQUIREMENTS_REL,
}

CANDIDATE_INTERNAL_GRAPH: Final = {
    "SOURCE_MANIFEST": {"phase": 0, "binds": []},
    "EXECUTION_PREFLIGHT": {"phase": 1, "binds": ["SOURCE_MANIFEST"]},
    "REVIEWED_TRUST_ANCHORS": {"phase": 1, "binds": ["SOURCE_MANIFEST"]},
    "ROLLBACK_INVENTORY": {"phase": 1, "binds": ["SOURCE_MANIFEST"]},
    "CUSTODY_PAYLOAD": {"phase": 1, "binds": ["SOURCE_MANIFEST"]},
    "HISTORY_SHARDS": {"phase": 1, "binds": ["SOURCE_MANIFEST"]},
    "CONSUMER_SOURCE_MAP": {"phase": 1, "binds": ["SOURCE_MANIFEST"]},
    "CUSTODY_MANIFEST": {
        "phase": 2,
        "binds": ["SOURCE_MANIFEST", "CUSTODY_PAYLOAD"],
    },
    "RECONSTRUCTION_RESULT": {
        "phase": 2,
        "binds": ["SOURCE_MANIFEST", "CUSTODY_PAYLOAD"],
    },
    "HISTORY_INDEX": {
        "phase": 3,
        "binds": [
            "SOURCE_MANIFEST",
            "HISTORY_SHARDS",
            "CONSUMER_SOURCE_MAP",
            "CUSTODY_MANIFEST",
        ],
    },
    "CURRENT_PROJECTION": {
        "phase": 4,
        "binds": ["SOURCE_MANIFEST", "HISTORY_INDEX"],
    },
    "RUNTIME_TRACE": {
        "phase": 5,
        "binds": [
            "SOURCE_MANIFEST",
            "HISTORY_INDEX",
            "CURRENT_PROJECTION",
        ],
    },
    "WRITER_PROBE": {
        "phase": 5,
        "binds": ["SOURCE_MANIFEST", "CURRENT_PROJECTION"],
    },
    "CONTROL_EVIDENCE": {
        "phase": 6,
        "binds": [
            "SOURCE_MANIFEST",
            "CURRENT_PROJECTION",
            "RUNTIME_TRACE",
            "WRITER_PROBE",
        ],
    },
    "RUNTIME_TRACE_MANIFEST": {
        "phase": 6,
        "binds": ["SOURCE_MANIFEST", "RUNTIME_TRACE"],
    },
    "VALIDATION_REPORT": {
        "phase": 7,
        "binds": [
            "SOURCE_MANIFEST",
            "CURRENT_PROJECTION",
            "CONTROL_EVIDENCE",
            "RUNTIME_TRACE_MANIFEST",
        ],
    },
}

SUCCESSOR_NEGATIVE_CONTROLS: Final = [
    (
        "DAG-V1-NC-001",
        "source_manifest_inventories_runtime_manifest",
        V0_CYCLE_ERROR,
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


class SuccessorPreparationError(ValueError):
    """The successor preparation contract or a frozen input is inconsistent."""


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(
            value,
            indent=2,
            sort_keys=True,
            ensure_ascii=False,
            allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")


def compact_json_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")


def _git_blob(commit: str, relative: str) -> bytes:
    result = subprocess.run(
        ["git", "show", f"{commit}:{relative}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
    )
    if result.returncode:
        raise SuccessorPreparationError(
            f"unavailable committed input {commit}:{relative}: "
            f"{result.stderr.decode('utf-8', errors='replace')}"
        )
    return result.stdout


def _git_oid(commit: str, relative: str) -> str:
    result = subprocess.run(
        ["git", "rev-parse", f"{commit}:{relative}"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode:
        raise SuccessorPreparationError(f"unavailable Git object {commit}:{relative}")
    return result.stdout.strip()


def _git_path_exists(commit: str, relative: str) -> bool:
    result = subprocess.run(
        ["git", "cat-file", "-e", f"{commit}:{relative}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
    )
    return result.returncode == 0


def _input_bindings() -> dict[str, dict[str, Any]]:
    rows: dict[str, dict[str, Any]] = {}
    for relative, (expected_sha, expected_oid, expected_size) in EXPECTED_INPUTS.items():
        raw = _git_blob(SOURCE_COMMIT, relative)
        observed = (sha256(raw), _git_oid(SOURCE_COMMIT, relative), len(raw))
        if observed != (expected_sha, expected_oid, expected_size):
            raise SuccessorPreparationError(
                f"frozen input mismatch for {relative}: {observed!r}"
            )
        rows[relative] = {
            "git_blob": expected_oid,
            "path": relative,
            "sha256": expected_sha,
            "size_bytes": expected_size,
            "source_commit": SOURCE_COMMIT,
        }
    return rows


def _closed(properties: dict[str, Any], required: list[str] | None = None) -> dict[str, Any]:
    return {
        "additionalProperties": False,
        "properties": properties,
        "required": required if required is not None else list(properties),
        "type": "object",
    }


def _sha_schema() -> dict[str, Any]:
    return {"pattern": "^[0-9a-f]{64}$", "type": "string"}


def _commit_schema() -> dict[str, Any]:
    return {"pattern": "^[0-9a-f]{40}$", "type": "string"}


def _path_schema() -> dict[str, Any]:
    return {
        "maxLength": 240,
        "minLength": 1,
        "pattern": (
            r"^(?!/)(?!.*//)(?![.]{1,2}(?:/|$))"
            r"(?!.*(?:/[.]{1,2})(?:/|$))(?!.*[\\:\x00-\x1f*?<>|\"])"
            r"(?![^/]*[. ](?:/|$))(?!.*[/][^/]*[. ](?:/|$))[^/]+(?:/[^/]+)*$"
        ),
        "type": "string",
    }


def _identity_schema() -> dict[str, Any]:
    return _closed(
        {
            "path": _path_schema(),
            "sha256": _sha_schema(),
            "size_bytes": {"minimum": 0, "type": "integer"},
        }
    )


def _git_identity_schema() -> dict[str, Any]:
    return _closed(
        {
            "git_blob": _commit_schema(),
            "git_commit": _commit_schema(),
            "path": _path_schema(),
            "sha256": _sha_schema(),
            "size_bytes": {"minimum": 0, "type": "integer"},
        }
    )


def _candidate_row_schema() -> dict[str, Any]:
    return _closed(
        {
            "artifact_kind": {
                "enum": [
                    "CURRENT_PROJECTION",
                    "HISTORY_INDEX",
                    "HISTORY_SHARD",
                    "CUSTODY_PAYLOAD",
                ],
                "type": "string",
            },
            "path": _path_schema(),
            "sha256": _sha_schema(),
            "size_bytes": {"minimum": 0, "type": "integer"},
        }
    )


def _evidence_row_schema() -> dict[str, Any]:
    return _closed(
        {
            "artifact_kind": {
                "enum": [
                    "CUSTODY_MANIFEST",
                    "RECONSTRUCTION_RESULT",
                    "CONSUMER_SOURCE_MAP",
                    "EXECUTION_PREFLIGHT",
                    "REVIEWED_TRUST_ANCHORS",
                    "RUNTIME_TRACE",
                    "RUNTIME_TRACE_MANIFEST",
                    "VALIDATION_REPORT",
                    "WRITER_PROBE",
                    "ROLLBACK_INVENTORY",
                    "CONTROL_EVIDENCE",
                ],
                "type": "string",
            },
            "path": _path_schema(),
            "sha256": _sha_schema(),
            "size_bytes": {"minimum": 0, "type": "integer"},
        }
    )


def _v0_stage_a_control_profiles() -> list[dict[str, Any]]:
    contract = json.loads(_git_blob(SOURCE_COMMIT, V0_CONTRACT_REL).decode("utf-8"))
    schema = contract["runtime_schemas"]["stage_a_precutover_report"]
    inherited = schema["properties"]["control_results"]["prefixItems"]
    runtime = schema["properties"]["runtime_contract_control_results"][
        "prefixItems"
    ]
    profiles = []
    for ordinal, row_schema in enumerate(inherited):
        properties = row_schema["properties"]
        profiles.append(
            {
                "control_family": "INHERITED_STAGE_A",
                "control_id": properties["control_id"]["const"],
                "expected_decision": properties["expected_decision"]["const"],
                "expected_error_codes": [
                    item["const"]
                    for item in properties["expected_error_codes"]["prefixItems"]
                ],
                "ordinal": ordinal,
                "source_contract_path": V0_CONTRACT_REL,
                "source_contract_sha256": EXPECTED_INPUTS[V0_CONTRACT_REL][0],
                "validator_profile": properties["validator_profile"]["const"],
            }
        )
    for offset, row_schema in enumerate(runtime):
        properties = row_schema["properties"]
        profiles.append(
            {
                "control_family": "RUNTIME_CONTRACT",
                "control_id": properties["control_id"]["const"],
                "expected_error": properties["expected_error"]["const"],
                "mutation": properties["mutation"]["const"],
                "ordinal": len(inherited) + offset,
                "source_contract_path": V0_CONTRACT_REL,
                "source_contract_sha256": EXPECTED_INPUTS[V0_CONTRACT_REL][0],
            }
        )
    control_ids = [row["control_id"] for row in profiles]
    if len(control_ids) != len(set(control_ids)) or len(control_ids) != 76:
        raise SuccessorPreparationError("v0 Stage-A control identity set is not 76 unique rows")
    if [row["control_family"] for row in profiles[:58]] != [
        "INHERITED_STAGE_A"
    ] * 58 or [row["control_family"] for row in profiles[58:]] != [
        "RUNTIME_CONTRACT"
    ] * 18:
        raise SuccessorPreparationError("v0 Stage-A control family partition drift")
    return profiles


def _stage_a_control_ids() -> list[str]:
    return [row["control_id"] for row in _v0_stage_a_control_profiles()]


def _control_profile_root(profiles: list[dict[str, Any]]) -> str:
    return sha256(
        b"LOOP_CONTROL_STAGE_A_V0_IMMUTABLE_CONTROL_PROFILE_ROOT_v1\0"
        + b"\n".join(compact_json_bytes(row) for row in profiles)
    )


def _control_result_root(rows: list[dict[str, Any]]) -> str:
    return sha256(
        b"LOOP_CONTROL_STAGE_A_76_CONTROL_RESULTS_ROOT_v1\0"
        + b"\n".join(compact_json_bytes(row) for row in rows)
    )


def _control_evidence_row_schemas(
    profiles: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    rows = []
    for profile in profiles:
        common = {
            "baseline_core_candidate_root_sha256": _sha_schema(),
            "control_family": {
                "const": profile["control_family"],
                "type": "string",
            },
            "control_id": {"const": profile["control_id"], "type": "string"},
            "passed": {"type": "boolean"},
        }
        if profile["control_family"] == "INHERITED_STAGE_A":
            row = _closed(
                {
                    **common,
                    "baseline_candidate_sha256_after": _sha_schema(),
                    "baseline_candidate_sha256_before": _sha_schema(),
                    "baseline_recreated_for_control": {"type": "boolean"},
                    "expected_decision": {
                        "const": profile["expected_decision"],
                        "type": "string",
                    },
                    "expected_error_codes": {
                        "const": profile["expected_error_codes"],
                        "type": "array",
                    },
                    "observed_decision": {"minLength": 1, "type": "string"},
                    "observed_error_codes": {
                        "items": {"minLength": 1, "type": "string"},
                        "type": "array",
                        "uniqueItems": True,
                    },
                    "positive_baseline_passed_before_mutation": {
                        "type": "boolean"
                    },
                    "subsequent_controls_received_unmodified_baseline": {
                        "type": "boolean"
                    },
                    "validator_profile": {
                        "const": profile["validator_profile"],
                        "type": "string",
                    },
                }
            )
        else:
            row = _closed(
                {
                    **common,
                    "expected_error": {
                        "const": profile["expected_error"],
                        "type": "string",
                    },
                    "fresh_baseline": {"type": "boolean"},
                    "mutation": {
                        "const": profile["mutation"],
                        "type": "string",
                    },
                    "observed_error": {"minLength": 1, "type": "string"},
                    "subsequent_controls_unmodified": {"type": "boolean"},
                }
            )
        rows.append(row)
    return rows


def _complete_control_result_overlays(
    profiles: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    overlays = []
    for profile in profiles:
        if profile["control_family"] == "INHERITED_STAGE_A":
            properties = {
                "baseline_recreated_for_control": {"const": True},
                "observed_decision": {"const": profile["expected_decision"]},
                "observed_error_codes": {
                    "const": profile["expected_error_codes"]
                },
                "passed": {"const": True},
                "positive_baseline_passed_before_mutation": {"const": True},
                "subsequent_controls_received_unmodified_baseline": {
                    "const": True
                },
            }
        else:
            properties = {
                "fresh_baseline": {"const": True},
                "observed_error": {"const": profile["expected_error"]},
                "passed": {"const": True},
                "subsequent_controls_unmodified": {"const": True},
            }
        overlays.append(
            {
                "properties": properties,
                "required": list(properties),
            }
        )
    return overlays


def build_runtime_schemas() -> dict[str, dict[str, Any]]:
    draft = "https://json-schema.org/draft/2020-12/schema"
    identity = _identity_schema()
    git_identity = _git_identity_schema()
    candidate_row = _candidate_row_schema()
    evidence_row = _evidence_row_schema()
    control_profiles = _v0_stage_a_control_profiles()
    control_ids = [row["control_id"] for row in control_profiles]
    preterminal_row = _closed(
        {
            "artifact_kind": {"minLength": 1, "type": "string"},
            "path": _path_schema(),
            "phase": {
                "enum": [
                    "IMMUTABLE_SOURCE",
                    "CANDIDATE",
                    "RUNTIME",
                    "EXECUTION_REPORT",
                ],
                "type": "string",
            },
            "sha256": _sha_schema(),
            "size_bytes": {"minimum": 0, "type": "integer"},
        }
    )
    source_manifest = _closed(
        {
            "schema_id": {
                "const": "LOOP_CONTROL_EXECUTION_SOURCE_MANIFEST_v2",
                "type": "string",
            },
            "manifest_version": {"const": 2, "type": "integer"},
            "hash_graph_id": {
                "const": "LOOP_CONTROL_STAGE_A_HASH_DAG_v1",
                "type": "string",
            },
            "generation_phase": {"const": "IMMUTABLE_INPUTS", "type": "string"},
            "successor_contract_review": git_identity,
            "source_commit": _commit_schema(),
            "implementation_commit": _commit_schema(),
            "implementation_tree_sha256": _sha_schema(),
            "fixed_execution_command": {
                "const": FIXED_EXECUTION_COMMAND,
                "type": "string",
            },
            "direct_production_test_node_id": {
                "const": DIRECT_TEST_NODE,
                "type": "string",
            },
            "source_registry": _closed(
                {
                    "git_blob": {
                        "const": EXPECTED_INPUTS[REGISTRY_REL][1],
                        "type": "string",
                    },
                    "git_commit": _commit_schema(),
                    "path": {"const": REGISTRY_REL, "type": "string"},
                    "sha256": {
                        "const": SOURCE_REGISTRY_SHA256,
                        "type": "string",
                    },
                    "size_bytes": {
                        "const": EXPECTED_INPUTS[REGISTRY_REL][2],
                        "type": "integer",
                    },
                }
            ),
            "authorized_inputs": {
                "items": _closed(
                    {
                        "git_blob": _commit_schema(),
                        "git_commit": _commit_schema(),
                        "path": _path_schema(),
                        "role": {
                            "enum": [
                                "SUCCESSOR_CONTRACT",
                                "CLOSED_SCHEMAS",
                                "PROTOCOL",
                                "ORCHESTRATOR",
                                "VALIDATOR",
                                "READER_API",
                                "PRODUCTION_CONTROL_TEST",
                                "SOURCE_REGISTRY",
                                "CONSUMER_SOURCE_MAP",
                                "REQUIREMENTS_LOCK",
                            ],
                            "type": "string",
                        },
                        "sha256": _sha_schema(),
                        "size_bytes": {"minimum": 1, "type": "integer"},
                    }
                ),
                "maxItems": 10,
                "minItems": 10,
                "type": "array",
                "uniqueItems": True,
            },
            "runtime_output_count": {"const": 0, "type": "integer"},
            "input_inventory_algorithm_id": {
                "const": "LOOP_CONTROL_STAGE_A_SOURCE_INPUT_INVENTORY_ROOT_v1",
                "type": "string",
            },
            "input_inventory_sha256": _sha_schema(),
            "allowed_output_specification_sha256": _sha_schema(),
            "deterministic": {"const": True, "type": "boolean"},
            "immutable": {"const": True, "type": "boolean"},
            "candidate_supplied_expectations_authoritative": {
                "const": False,
                "type": "boolean",
            },
            "stage_b_authorized": {"const": False, "type": "boolean"},
        }
    )
    runtime_manifest = _closed(
        {
            "schema_id": {
                "const": "LOOP_CONTROL_STAGE_A_RUNTIME_MANIFEST_v2",
                "type": "string",
            },
            "manifest_version": {"const": 2, "type": "integer"},
            "hash_graph_id": {
                "const": "LOOP_CONTROL_STAGE_A_HASH_DAG_v1",
                "type": "string",
            },
            "run_id": {
                "pattern": "^[A-Za-z0-9][A-Za-z0-9_-]{0,63}$",
                "type": "string",
            },
            "run_root_repo_relative": _path_schema(),
            "stage": {"const": "STAGE_A", "type": "string"},
            "implementation_commit": _commit_schema(),
            "source_manifest": identity,
            "source_registry_sha256": {
                "const": SOURCE_REGISTRY_SHA256,
                "type": "string",
            },
            "candidate_artifacts": {
                "items": candidate_row,
                "minItems": 1,
                "type": "array",
                "uniqueItems": True,
            },
            "candidate_artifact_count": {"minimum": 1, "type": "integer"},
            "candidate_artifact_root_sha256": _sha_schema(),
            "evidence_artifacts": {
                "items": evidence_row,
                "minItems": 1,
                "type": "array",
                "uniqueItems": True,
            },
            "evidence_artifact_count": {"minimum": 1, "type": "integer"},
            "evidence_artifact_root_sha256": _sha_schema(),
            "execution_command": {
                "const": FIXED_EXECUTION_COMMAND,
                "type": "string",
            },
            "started_at_utc": {"format": "date-time", "type": "string"},
            "finished_at_utc": {"format": "date-time", "type": "string"},
            "expected_control_count": {"const": 76, "type": "integer"},
            "observed_control_count": {
                "maximum": 76,
                "minimum": 0,
                "type": "integer",
            },
            "passed_control_count": {
                "maximum": 76,
                "minimum": 0,
                "type": "integer",
            },
            "control_evidence": identity,
            "direct_production_control_invocation": _closed(
                {
                    "command": {"const": DIRECT_TEST_COMMAND, "type": "string"},
                    "exit_code": {"type": "integer"},
                    "invoked": {"const": True, "type": "boolean"},
                    "stderr_sha256": _sha_schema(),
                    "stdout_sha256": _sha_schema(),
                    "test_node_id": {"const": DIRECT_TEST_NODE, "type": "string"},
                }
            ),
            "writer_probe": identity,
            "rollback_inventory": identity,
            "orchestrator_outcome": {
                "enum": [
                    "CANDIDATE_AND_CONTROLS_COMPLETE_PENDING_EXECUTION_REPORT",
                    "B_BLOCKED_STAGE_A_CANDIDATE_PRESERVED",
                ],
                "type": "string",
            },
            "block_reason_codes": {
                "items": {"minLength": 1, "type": "string"},
                "type": "array",
                "uniqueItems": True,
            },
            "write_outside_run_root_count": {"const": 0, "type": "integer"},
            "source_registry_modified": {"const": False, "type": "boolean"},
            "source_registry_sha256_before": {
                "const": SOURCE_REGISTRY_SHA256,
                "type": "string",
            },
            "source_registry_sha256_after": {
                "const": SOURCE_REGISTRY_SHA256,
                "type": "string",
            },
            "pre_run_detached_checkout_clean": {"const": True, "type": "boolean"},
            "only_allowlisted_changes_so_far": {"const": True, "type": "boolean"},
            "consumer_cutover_performed": {"const": False, "type": "boolean"},
            "stage_b_executed": {"const": False, "type": "boolean"},
            "immutable": {"const": True, "type": "boolean"},
        }
    )
    runtime_manifest["oneOf"] = [
        {
            "properties": {
                "direct_production_control_invocation": {
                    "properties": {"exit_code": {"const": 0}}
                },
                "block_reason_codes": {"const": []},
                "observed_control_count": {"const": 76},
                "orchestrator_outcome": {
                    "const": "CANDIDATE_AND_CONTROLS_COMPLETE_PENDING_EXECUTION_REPORT"
                },
                "passed_control_count": {"const": 76},
            },
            "required": [
                "direct_production_control_invocation",
                "block_reason_codes",
                "observed_control_count",
                "orchestrator_outcome",
                "passed_control_count",
            ],
        },
        {
            "properties": {
                "block_reason_codes": {"minItems": 1},
                "orchestrator_outcome": {
                    "const": "B_BLOCKED_STAGE_A_CANDIDATE_PRESERVED"
                }
            },
            "required": ["block_reason_codes", "orchestrator_outcome"],
        },
    ]
    execution_report = _closed(
        {
            "schema_id": {
                "const": "LOOP_CONTROL_STAGE_A_EXECUTION_REPORT_v2",
                "type": "string",
            },
            "report_version": {"const": 2, "type": "integer"},
            "hash_graph_id": {
                "const": "LOOP_CONTROL_STAGE_A_HASH_DAG_v1",
                "type": "string",
            },
            "run_id": {
                "pattern": "^[A-Za-z0-9][A-Za-z0-9_-]{0,63}$",
                "type": "string",
            },
            "implementation_commit": _commit_schema(),
            "source_manifest": identity,
            "runtime_manifest": identity,
            "candidate_artifact_root_sha256": _sha_schema(),
            "evidence_artifact_root_sha256": _sha_schema(),
            "control_evidence": identity,
            "control_results_root_algorithm_id": {
                "const": "LOOP_CONTROL_STAGE_A_76_CONTROL_RESULTS_ROOT_v1",
                "type": "string",
            },
            "control_results_root_sha256": _sha_schema(),
            "expected_control_count": {"const": 76, "type": "integer"},
            "observed_control_count": {
                "maximum": 76,
                "minimum": 0,
                "type": "integer",
            },
            "primary_controls_expected": {"const": 51, "type": "integer"},
            "primary_controls_observed": {
                "maximum": 51,
                "minimum": 0,
                "type": "integer",
            },
            "primary_controls_passed": {
                "maximum": 51,
                "minimum": 0,
                "type": "integer",
            },
            "readiness_controls_expected": {"const": 7, "type": "integer"},
            "readiness_controls_observed": {
                "maximum": 7,
                "minimum": 0,
                "type": "integer",
            },
            "readiness_controls_passed": {
                "maximum": 7,
                "minimum": 0,
                "type": "integer",
            },
            "runtime_contract_controls_expected": {"const": 18, "type": "integer"},
            "runtime_contract_controls_observed": {
                "maximum": 18,
                "minimum": 0,
                "type": "integer",
            },
            "runtime_contract_controls_passed": {
                "maximum": 18,
                "minimum": 0,
                "type": "integer",
            },
            "direct_production_control_invocation": _closed(
                {
                    "exit_code": {"type": "integer"},
                    "invoked": {"const": True, "type": "boolean"},
                    "test_node_id": {"const": DIRECT_TEST_NODE, "type": "string"},
                }
            ),
            "stdout_sha256": _sha_schema(),
            "stderr_sha256": _sha_schema(),
            "exit_code": {"type": "integer"},
            "source_registry_unchanged": {"const": True, "type": "boolean"},
            "consumer_cutover_performed": {"const": False, "type": "boolean"},
            "authority_cutover_performed": {"const": False, "type": "boolean"},
            "stage_b_behavior_observed": {"const": False, "type": "boolean"},
            "block_reason_codes": {
                "items": {"minLength": 1, "type": "string"},
                "type": "array",
                "uniqueItems": True,
            },
            "all_controls_passed": {"type": "boolean"},
            "status": {
                "enum": [
                    "STAGE_A_CANDIDATE_COMPLETE_PENDING_TERMINAL_ENVELOPE",
                    "B_BLOCKED_STAGE_A_CANDIDATE_PRESERVED",
                ],
                "type": "string",
            },
            "stage_b_authorized": {"const": False, "type": "boolean"},
        }
    )
    execution_report["oneOf"] = [
        {
            "properties": {
                "all_controls_passed": {"const": True},
                "block_reason_codes": {"const": []},
                "direct_production_control_invocation": {
                    "properties": {"exit_code": {"const": 0}}
                },
                "exit_code": {"const": 0},
                "observed_control_count": {"const": 76},
                "primary_controls_observed": {"const": 51},
                "primary_controls_passed": {"const": 51},
                "readiness_controls_observed": {"const": 7},
                "readiness_controls_passed": {"const": 7},
                "runtime_contract_controls_observed": {"const": 18},
                "runtime_contract_controls_passed": {"const": 18},
                "status": {
                    "const": "STAGE_A_CANDIDATE_COMPLETE_PENDING_TERMINAL_ENVELOPE"
                },
            },
            "required": [
                "all_controls_passed",
                "block_reason_codes",
                "direct_production_control_invocation",
                "exit_code",
                "observed_control_count",
                "primary_controls_observed",
                "primary_controls_passed",
                "readiness_controls_observed",
                "readiness_controls_passed",
                "runtime_contract_controls_observed",
                "runtime_contract_controls_passed",
                "status",
            ],
        },
        {
            "properties": {
                "all_controls_passed": {"const": False},
                "block_reason_codes": {"minItems": 1},
                "status": {"const": "B_BLOCKED_STAGE_A_CANDIDATE_PRESERVED"},
            },
            "required": ["all_controls_passed", "block_reason_codes", "status"],
        },
    ]
    control_evidence = _closed(
        {
            "schema_id": {
                "const": "LOOP_CONTROL_STAGE_A_CONTROL_EVIDENCE_v1",
                "type": "string",
            },
            "evidence_version": {"const": 1, "type": "integer"},
            "run_id": {
                "pattern": "^[A-Za-z0-9][A-Za-z0-9_-]{0,63}$",
                "type": "string",
            },
            "control_ids": {"const": control_ids, "type": "array"},
            "control_results": {
                "items": False,
                "maxItems": 76,
                "minItems": 76,
                "prefixItems": _control_evidence_row_schemas(control_profiles),
                "type": "array",
            },
            "control_result_count": {"const": 76, "type": "integer"},
            "baseline_core_candidate_root_sha256": _sha_schema(),
            "primary_control_count": {"const": 51, "type": "integer"},
            "readiness_control_count": {"const": 7, "type": "integer"},
            "runtime_contract_control_count": {"const": 18, "type": "integer"},
            "results_root_algorithm_id": {
                "const": "LOOP_CONTROL_STAGE_A_76_CONTROL_RESULTS_ROOT_v1",
                "type": "string",
            },
            "results_root_sha256": _sha_schema(),
            "direct_production_control_invocation": _closed(
                {
                    "command": {"const": DIRECT_TEST_COMMAND, "type": "string"},
                    "exit_code": {"type": "integer"},
                    "stderr_sha256": _sha_schema(),
                    "stdout_sha256": _sha_schema(),
                    "test_node_id": {"const": DIRECT_TEST_NODE, "type": "string"},
                }
            ),
            "baseline_isolation_verified": {"type": "boolean"},
            "all_results_passed": {"type": "boolean"},
            "block_reason_codes": {
                "items": {"minLength": 1, "type": "string"},
                "type": "array",
                "uniqueItems": True,
            },
            "status": {
                "enum": ["ALL_76_CONTROLS_PASSED", "B_BLOCKED"],
                "type": "string",
            },
        }
    )
    control_evidence["oneOf"] = [
        {
            "properties": {
                "all_results_passed": {"const": True},
                "baseline_isolation_verified": {"const": True},
                "block_reason_codes": {"const": []},
                "control_results": {
                    "items": False,
                    "maxItems": 76,
                    "minItems": 76,
                    "prefixItems": _complete_control_result_overlays(
                        control_profiles
                    ),
                },
                "direct_production_control_invocation": {
                    "properties": {"exit_code": {"const": 0}}
                },
                "status": {"const": "ALL_76_CONTROLS_PASSED"},
            },
            "required": [
                "all_results_passed",
                "baseline_isolation_verified",
                "block_reason_codes",
                "control_results",
                "direct_production_control_invocation",
                "status",
            ],
        },
        {
            "properties": {
                "all_results_passed": {"const": False},
                "block_reason_codes": {"minItems": 1},
                "control_results": {
                    "contains": {
                        "properties": {"passed": {"const": False}},
                        "required": ["passed"],
                    },
                    "minContains": 1,
                },
                "status": {"const": "B_BLOCKED"},
            },
            "required": [
                "all_results_passed",
                "block_reason_codes",
                "control_results",
                "status",
            ],
        },
    ]
    terminal_envelope = _closed(
        {
            "schema_id": {
                "const": "LOOP_CONTROL_STAGE_A_TERMINAL_EXECUTION_ENVELOPE_v1",
                "type": "string",
            },
            "envelope_version": {"const": 1, "type": "integer"},
            "hash_graph_id": {
                "const": "LOOP_CONTROL_STAGE_A_HASH_DAG_v1",
                "type": "string",
            },
            "run_id": {
                "pattern": "^[A-Za-z0-9][A-Za-z0-9_-]{0,63}$",
                "type": "string",
            },
            "stage": {"const": "STAGE_A", "type": "string"},
            "implementation_commit": _commit_schema(),
            "source_manifest": identity,
            "runtime_manifest": identity,
            "execution_report": identity,
            "control_evidence": identity,
            "candidate_artifacts": {
                "items": candidate_row,
                "minItems": 1,
                "type": "array",
                "uniqueItems": True,
            },
            "candidate_artifact_count": {"minimum": 1, "type": "integer"},
            "candidate_shard_count": {"minimum": 1, "type": "integer"},
            "candidate_artifact_root_sha256": _sha_schema(),
            "evidence_artifacts": {
                "items": evidence_row,
                "minItems": 1,
                "type": "array",
                "uniqueItems": True,
            },
            "evidence_artifact_count": {"minimum": 1, "type": "integer"},
            "evidence_artifact_root_sha256": _sha_schema(),
            "preterminal_inventory_algorithm_id": {
                "const": "LOOP_CONTROL_STAGE_A_PRETERMINAL_INVENTORY_ROOT_v1",
                "type": "string",
            },
            "preterminal_artifact_count": {"minimum": 1, "type": "integer"},
            "preterminal_artifacts": {
                "items": preterminal_row,
                "minItems": 1,
                "type": "array",
                "uniqueItems": True,
            },
            "preterminal_inventory_root_sha256": _sha_schema(),
            "control_results_root_algorithm_id": {
                "const": "LOOP_CONTROL_STAGE_A_76_CONTROL_RESULTS_ROOT_v1",
                "type": "string",
            },
            "control_results_root_sha256": _sha_schema(),
            "source_registry_sha256": {
                "const": SOURCE_REGISTRY_SHA256,
                "type": "string",
            },
            "candidate_status": {
                "enum": [
                    "STAGE_A_CANDIDATE_COMPLETE_PENDING_INDEPENDENT_REVIEW",
                    "B_BLOCKED_STAGE_A_CANDIDATE_PRESERVED",
                ],
                "type": "string",
            },
            "block_reason_codes": {
                "items": {"minLength": 1, "type": "string"},
                "type": "array",
                "uniqueItems": True,
            },
            "control_summary": _closed(
                {
                    "all_expected_control_ids_accounted_for": {"type": "boolean"},
                    "direct_production_test_invoked": {
                        "const": True,
                        "type": "boolean",
                    },
                    "expected": {"const": 76, "type": "integer"},
                    "observed": {
                        "maximum": 76,
                        "minimum": 0,
                        "type": "integer",
                    },
                    "passed": {
                        "maximum": 76,
                        "minimum": 0,
                        "type": "integer",
                    },
                }
            ),
            "integrity_summary": _closed(
                {
                    "byte_exact_reconstruction": {"type": "boolean"},
                    "candidate_hashes_externally_adjudicated": {"type": "boolean"},
                    "no_write_outside_run_root": {"const": True, "type": "boolean"},
                    "preterminal_coverage_complete": {"const": True, "type": "boolean"},
                    "source_registry_unchanged": {"const": True, "type": "boolean"},
                }
            ),
            "nonpromotion": _closed(
                {
                    "authority_cutover_authorized": {"const": False, "type": "boolean"},
                    "consumer_migration_authorized": {"const": False, "type": "boolean"},
                    "independent_review_required": {"const": True, "type": "boolean"},
                    "monolith_retirement_authorized": {"const": False, "type": "boolean"},
                    "scientific_target_rotation_authorized": {"const": False, "type": "boolean"},
                    "stage_b_authorized": {"const": False, "type": "boolean"},
                    "unit_ledger_execution_authorized": {"const": False, "type": "boolean"},
                }
            ),
            "terminal": {"const": True, "type": "boolean"},
            "stage_b_authorized": {"const": False, "type": "boolean"},
            "immutable": {"const": True, "type": "boolean"},
        }
    )
    terminal_envelope["oneOf"] = [
        {
            "properties": {
                "candidate_status": {
                    "const": "STAGE_A_CANDIDATE_COMPLETE_PENDING_INDEPENDENT_REVIEW"
                },
                "block_reason_codes": {"const": []},
                "control_summary": {
                    "properties": {
                        "all_expected_control_ids_accounted_for": {"const": True},
                        "observed": {"const": 76},
                        "passed": {"const": 76},
                    }
                },
                "integrity_summary": {
                    "properties": {
                        "byte_exact_reconstruction": {"const": True},
                        "candidate_hashes_externally_adjudicated": {"const": True},
                    }
                },
            },
            "required": [
                "candidate_status",
                "block_reason_codes",
                "control_summary",
                "integrity_summary",
            ],
        },
        {
            "properties": {
                "candidate_status": {
                    "const": "B_BLOCKED_STAGE_A_CANDIDATE_PRESERVED"
                },
                "block_reason_codes": {"minItems": 1},
                "control_summary": {
                    "properties": {"passed": {"maximum": 75}}
                },
            },
            "required": ["block_reason_codes", "candidate_status", "control_summary"],
        },
    ]
    preflight_diagnostic = _closed(
        {
            "schema_id": {
                "const": "LOOP_CONTROL_STAGE_A_PREFLIGHT_DIAGNOSTIC_v1",
                "type": "string",
            },
            "classification": {
                "enum": [
                    "blocked_preflight_contract_unsatisfiable",
                    "blocked_preflight_external_trust_mismatch",
                    "blocked_preflight_worktree_or_git_mismatch",
                    "blocked_preflight_implementation_scope_mismatch",
                    "blocked_preflight_source_registry_mismatch",
                    "blocked_preflight_path_safety_mismatch",
                ],
                "type": "string",
            },
            "error_code": {"minLength": 1, "type": "string"},
            "message": {"minLength": 1, "type": "string"},
            "candidate_set_created": {"const": False, "type": "boolean"},
            "prototype_run_root_created": {"const": False, "type": "boolean"},
            "source_registry_sha256_before": {
                "const": SOURCE_REGISTRY_SHA256,
                "type": "string",
            },
            "source_registry_sha256_after": {
                "const": SOURCE_REGISTRY_SHA256,
                "type": "string",
            },
            "controls_observed": {"const": 0, "type": "integer"},
        }
    )
    independent_review_binding = _closed(
        {
            "schema_id": {
                "const": "LOOP_CONTROL_STAGE_A_INDEPENDENT_REVIEW_BINDING_v1",
                "type": "string",
            },
            "execution_commit": _commit_schema(),
            "terminal_envelope": git_identity,
            "terminal_envelope_required": {"const": True, "type": "boolean"},
            "successor_regression_controls_observed": {
                "const": 12,
                "type": "integer",
            },
            "successor_regression_control_results": {
                "items": False,
                "maxItems": 12,
                "minItems": 12,
                "prefixItems": [
                    _closed(
                        {
                            "baseline_recreated": {
                                "const": True,
                                "type": "boolean",
                            },
                            "control_id": {"const": control_id, "type": "string"},
                            "expected_error_code": {
                                "const": error_code,
                                "type": "string",
                            },
                            "mutation": {"const": mutation, "type": "string"},
                            "observed_error_code": {
                                "const": error_code,
                                "type": "string",
                            },
                            "passed": {"const": True, "type": "boolean"},
                            "subsequent_controls_unmodified": {
                                "const": True,
                                "type": "boolean",
                            },
                        }
                    )
                    for control_id, mutation, error_code in SUCCESSOR_NEGATIVE_CONTROLS
                ],
                "type": "array",
            },
            "successor_regression_results_root_sha256": _sha_schema(),
            "fresh_baseline_isolation_verified": {"const": True, "type": "boolean"},
            "execution_report_status": {
                "enum": [
                    "STAGE_A_CANDIDATE_COMPLETE_PENDING_TERMINAL_ENVELOPE",
                    "B_BLOCKED_STAGE_A_CANDIDATE_PRESERVED",
                ],
                "type": "string",
            },
            "terminal_candidate_status": {
                "enum": [
                    "STAGE_A_CANDIDATE_COMPLETE_PENDING_INDEPENDENT_REVIEW",
                    "B_BLOCKED_STAGE_A_CANDIDATE_PRESERVED",
                ],
                "type": "string",
            },
            "decision": {
                "enum": ["ACCEPT_STAGE_A_CANDIDATE_ONLY", "B_BLOCKED"],
                "type": "string",
            },
            "stage_b_authorized": {"const": False, "type": "boolean"},
        }
    )
    independent_review_binding["oneOf"] = [
        {
            "properties": {
                "decision": {"const": "ACCEPT_STAGE_A_CANDIDATE_ONLY"},
                "execution_report_status": {
                    "const": "STAGE_A_CANDIDATE_COMPLETE_PENDING_TERMINAL_ENVELOPE"
                },
                "terminal_candidate_status": {
                    "const": "STAGE_A_CANDIDATE_COMPLETE_PENDING_INDEPENDENT_REVIEW"
                },
            },
            "required": [
                "decision",
                "execution_report_status",
                "terminal_candidate_status",
            ],
        },
        {
            "properties": {"decision": {"const": "B_BLOCKED"}},
            "required": ["decision"],
        },
    ]
    schemas = {
        "execution_source_manifest": source_manifest,
        "runtime_manifest": runtime_manifest,
        "control_evidence": control_evidence,
        "execution_report": execution_report,
        "terminal_execution_envelope": terminal_envelope,
        "preflight_diagnostic": preflight_diagnostic,
        "stage_a_independent_review_binding": independent_review_binding,
    }
    for name, schema in schemas.items():
        schema["$id"] = f"https://toe.local/schema/registry-stage-a-v1/{name}.json"
        schema["$schema"] = draft
        Draft202012Validator.check_schema(schema)
    return schemas


def positive_hash_graph() -> dict[str, Any]:
    return {
        "edge_semantics": "NODE_BINDS_ONLY_HASHES_OF_NODES_LISTED_IN_BINDS",
        "nodes": [
            {
                "binds": list(GRAPH_BINDS[node]),
                "node_id": node,
                "ordinal": ordinal,
            }
            for ordinal, node in enumerate(GRAPH_ORDER)
        ],
        "topological_order": list(GRAPH_ORDER),
    }


def validate_hash_graph(graph: dict[str, Any]) -> None:
    nodes = graph.get("nodes")
    if not isinstance(nodes, list):
        raise SuccessorPreparationError("hash graph nodes must be a list")
    ids = [row.get("node_id") for row in nodes if isinstance(row, dict)]
    if ids != GRAPH_ORDER or len(ids) != len(set(ids)):
        raise SuccessorPreparationError("hash graph node order or identity differs")
    ordinals = {row["node_id"]: row["ordinal"] for row in nodes}
    if [ordinals[node] for node in GRAPH_ORDER] != list(range(len(GRAPH_ORDER))):
        raise SuccessorPreparationError("hash graph ordinals are not contiguous")
    for row in nodes:
        node = row["node_id"]
        if row["binds"] != GRAPH_BINDS[node]:
            raise SuccessorPreparationError(f"hash graph bindings differ for {node}")
        for dependency in row["binds"]:
            if dependency == node:
                raise SuccessorPreparationError(f"self-reference at {node}")
            if dependency not in ordinals or ordinals[dependency] >= ordinals[node]:
                raise SuccessorPreparationError(
                    f"backward or unknown binding {node} -> {dependency}"
                )
    if graph.get("topological_order") != GRAPH_ORDER:
        raise SuccessorPreparationError("topological order differs")


def validate_candidate_internal_graph(graph: dict[str, dict[str, Any]]) -> None:
    if set(graph) != set(CANDIDATE_INTERNAL_GRAPH):
        raise SuccessorPreparationError("candidate-internal graph node set differs")
    for node, row in graph.items():
        if row != CANDIDATE_INTERNAL_GRAPH[node]:
            raise SuccessorPreparationError(f"candidate-internal graph differs for {node}")
        phase = row["phase"]
        for dependency in row["binds"]:
            if dependency == node:
                raise SuccessorPreparationError(f"candidate self-reference at {node}")
            if dependency not in graph or graph[dependency]["phase"] >= phase:
                raise SuccessorPreparationError(
                    f"candidate cycle/back-edge {node} -> {dependency}"
                )


def positive_successor_fixture() -> dict[str, Any]:
    shards = [
        "history/shards/LOOP_CONTROL_HISTORY_0000.jsonl",
        "history/shards/LOOP_CONTROL_HISTORY_0001.jsonl",
    ]
    candidate_paths = [
        "projection/LOOP_CONTROL_CURRENT_v1.prototype.json",
        "history/LOOP_CONTROL_HISTORY_INDEX_v1.prototype.json",
        *shards,
        "custody/LOOP_CONTROL_LEGACY_BYTE_CUSTODY_v1.json.gz",
    ]
    return {
        "source_manifest": {
            "inventoried_roles": [
                "SUCCESSOR_CONTRACT",
                "CLOSED_SCHEMAS",
                "PROTOCOL",
                "ORCHESTRATOR",
                "VALIDATOR",
                "READER_API",
                "PRODUCTION_CONTROL_TEST",
                "SOURCE_REGISTRY",
                "CONSUMER_SOURCE_MAP",
                "REQUIREMENTS_LOCK",
            ],
            "nondeterministic_fields": [],
            "sha256": "1" * 64,
        },
        "candidate": {
            "external_expected_source_sha256": SOURCE_REGISTRY_SHA256,
            "finalized": True,
            "paths": candidate_paths,
            "shards": shards,
        },
        "runtime_manifest": {
            "binds_source_manifest": True,
            "candidate_finalized_before_manifest": True,
            "candidate_paths": list(candidate_paths),
            "includes_terminal_envelope": False,
            "source_manifest_sha256": "1" * 64,
        },
        "execution_report": {
            "binds_terminal_envelope": False,
            "run_id": "stage_a_v1",
        },
        "terminal_envelope": {
            "candidate_paths": list(candidate_paths),
            "execution_report_run_id": "stage_a_v1",
            "hashes_itself": False,
            "included_in_earlier_manifest": False,
            "run_id": "stage_a_v1",
        },
        "review": {"terminal_envelope_present": True},
    }


def validate_successor_fixture(fixture: dict[str, Any]) -> str | None:
    source = fixture["source_manifest"]
    candidate = fixture["candidate"]
    runtime = fixture["runtime_manifest"]
    report = fixture["execution_report"]
    terminal = fixture["terminal_envelope"]
    review = fixture["review"]
    forbidden_source_roles = {
        "RUNTIME_MANIFEST",
        "CANDIDATE_ARTIFACT",
        "EXECUTION_REPORT",
        "TERMINAL_ENVELOPE",
        "STAGE_A_INDEPENDENT_REVIEW",
    }
    if forbidden_source_roles.intersection(source["inventoried_roles"]):
        return V0_CYCLE_ERROR
    if not runtime["binds_source_manifest"]:
        return "V1-E-RUNTIME-SOURCE-MANIFEST-BINDING-MISSING"
    if runtime["source_manifest_sha256"] != source["sha256"]:
        return "V1-E-RUNTIME-SOURCE-MANIFEST-BINDING-MISMATCH"
    if terminal["included_in_earlier_manifest"] or runtime["includes_terminal_envelope"]:
        return "V1-E-HASH-DAG-FORWARD-REFERENCE"
    if terminal["hashes_itself"]:
        return "V1-E-TERMINAL-ENVELOPE-SELF-REFERENCE"
    if report["binds_terminal_envelope"]:
        return "V1-E-EXECUTION-TERMINAL-CYCLE"
    if candidate["external_expected_source_sha256"] != SOURCE_REGISTRY_SHA256:
        return "V1-E-EXTERNAL-TRUST-ROOT-REBIND"
    if not candidate["finalized"] or not runtime["candidate_finalized_before_manifest"]:
        return "V1-E-RUNTIME-MANIFEST-INCOMPLETE-CANDIDATE-SET"
    if source["nondeterministic_fields"]:
        return "V1-E-SOURCE-MANIFEST-NONDETERMINISTIC-FIELD"
    if not review["terminal_envelope_present"]:
        return "V1-E-REVIEW-MISSING-TERMINAL-ENVELOPE"
    if set(terminal["candidate_paths"]) != set(runtime["candidate_paths"]):
        return "V1-E-TERMINAL-CANDIDATE-COVERAGE"
    if terminal["execution_report_run_id"] != terminal["run_id"]:
        return "V1-E-TERMINAL-CROSS-RUN-BINDING"
    return None


def mutate_fixture(fixture: dict[str, Any], mutation: str) -> None:
    if mutation == "source_manifest_inventories_runtime_manifest":
        fixture["source_manifest"]["inventoried_roles"].append("RUNTIME_MANIFEST")
    elif mutation == "runtime_manifest_omits_source_manifest_binding":
        fixture["runtime_manifest"]["binds_source_manifest"] = False
    elif mutation == "runtime_manifest_binds_modified_source_manifest":
        fixture["runtime_manifest"]["source_manifest_sha256"] = "2" * 64
    elif mutation == "terminal_envelope_included_in_earlier_manifest":
        fixture["runtime_manifest"]["includes_terminal_envelope"] = True
    elif mutation == "terminal_envelope_hashes_itself":
        fixture["terminal_envelope"]["hashes_itself"] = True
    elif mutation == "execution_report_and_terminal_bind_reciprocally":
        fixture["execution_report"]["binds_terminal_envelope"] = True
    elif mutation == "candidate_rebinds_external_expected_source_hash":
        fixture["candidate"]["external_expected_source_sha256"] = "3" * 64
    elif mutation == "runtime_manifest_precedes_candidate_finalization":
        fixture["runtime_manifest"]["candidate_finalized_before_manifest"] = False
    elif mutation == "source_manifest_contains_temporary_or_wall_clock_field":
        fixture["source_manifest"]["nondeterministic_fields"] = ["temporary_path"]
    elif mutation == "review_accepts_chain_without_terminal_envelope":
        fixture["review"]["terminal_envelope_present"] = False
    elif mutation == "terminal_envelope_omits_candidate_shard":
        omitted = fixture["candidate"]["shards"][-1]
        fixture["terminal_envelope"]["candidate_paths"].remove(omitted)
    elif mutation == "terminal_envelope_binds_execution_report_from_other_run":
        fixture["terminal_envelope"]["execution_report_run_id"] = "other_run"
    else:
        raise SuccessorPreparationError(f"unknown successor mutation: {mutation}")


def run_successor_negative_controls() -> list[dict[str, Any]]:
    baseline = positive_successor_fixture()
    if validate_successor_fixture(baseline) is not None:
        raise SuccessorPreparationError("positive successor fixture does not pass")
    baseline_sha = sha256(compact_json_bytes(baseline))
    results: list[dict[str, Any]] = []
    for control_id, mutation, expected in SUCCESSOR_NEGATIVE_CONTROLS:
        candidate = deepcopy(baseline)
        mutate_fixture(candidate, mutation)
        observed = validate_successor_fixture(candidate)
        results.append(
            {
                "baseline_recreated": True,
                "baseline_sha256_after": baseline_sha,
                "baseline_sha256_before": baseline_sha,
                "control_id": control_id,
                "expected_error_code": expected,
                "mutation": mutation,
                "observed_error_code": observed,
                "passed": observed == expected,
                "subsequent_controls_unmodified": True,
            }
        )
    if not all(row["passed"] for row in results):
        raise SuccessorPreparationError("one or more successor negative controls failed")
    return results


def _control_root(results: list[dict[str, Any]]) -> str:
    return sha256(
        b"LOOP_CONTROL_STAGE_A_V1_SUCCESSOR_REGRESSION_ROOT\0"
        + b"\n".join(compact_json_bytes(row) for row in results)
    )


def build_contract() -> dict[str, Any]:
    bindings = _input_bindings()
    graph = positive_hash_graph()
    validate_hash_graph(graph)
    validate_candidate_internal_graph(deepcopy(CANDIDATE_INTERNAL_GRAPH))
    controls = run_successor_negative_controls()
    schemas = build_runtime_schemas()
    stage_a_profiles = _v0_stage_a_control_profiles()
    stage_a_ids = [row["control_id"] for row in stage_a_profiles]
    return {
        "authorization": {
            "consumer_migration_authorized": False,
            "current_authority_cutover_authorized": False,
            "implementation_change_authorized_before_independent_review": False,
            "maintenance_target_rotation_authorized": False,
            "monolith_modification_or_retirement_authorized": False,
            "new_api_writes_authorized": False,
            "packet_independent_review_required": True,
            "prototype_execution_authorized": False,
            "registry_migration_execution_authorized": False,
            "scientific_target_rotation_authorized": False,
            "stage_b_authorized": False,
            "unit_ledger_execution_authorized": False,
        },
        "captured_at_utc": CAPTURED_AT_UTC,
        "external_trust_contract": {
            "candidate_values_may_redefine_expected_hashes": False,
            "execution_source_manifest_must_bind": [
                "SUCCESSOR_CONTRACT_INDEPENDENT_REVIEW_FROM_GIT",
                "SUCCESSOR_CONTRACT_AND_SCHEMA_HASHES",
                "SOURCE_REGISTRY_HASH",
                "AUTHORIZED_IMPLEMENTATION_COMMIT_AND_FILE_HASHES",
                "CONSUMER_SOURCE_MAP_HASH",
                "REQUIREMENTS_LOCK_HASH",
            ],
            "frozen_preparation_inputs": bindings,
            "successor_review_hash_known_only_after_review": True,
            "successor_review_must_be_an_ancestor_of_implementation_commit": True,
        },
        "failure_semantics": {
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
        },
        "generation_order": [
            "VERIFY_EXTERNAL_TRUST_ROOTS",
            "WRITE_IMMUTABLE_SOURCE_MANIFEST",
            "GENERATE_AND_FINALIZE_CANDIDATE_ARTIFACTS",
            "WRITE_RUNTIME_MANIFEST",
            "WRITE_STAGE_A_EXECUTION_REPORT",
            "WRITE_TERMINAL_EXECUTION_ENVELOPE",
            "RUN_POSTTERMINAL_DAG_REGRESSION_CONTROLS",
            "INDEPENDENT_REVIEW_BINDS_TERMINAL_ENVELOPE",
        ],
        "hash_graph_contract": {
            **graph,
            "acyclic": True,
            "earlier_artifact_may_bind_later_artifact": False,
            "no_artifact_may_bind_itself": True,
            "source_manifest_may_bind_runtime_outputs": False,
            "terminal_envelope_has_no_outgoing_runtime_hash_dependency": True,
        },
        "candidate_internal_hash_graph": {
            "dependency_semantics": "NODE_BINDS_ONLY_EARLIER_PHASE_NODES",
            "nodes": deepcopy(CANDIDATE_INTERNAL_GRAPH),
            "no_candidate_root_may_be_embedded_IN_ARTIFACTS_USED_TO_COMPUTE_THAT_ROOT": True,
            "projection_may_not_bind_history_index_that_also_binds_projection": True,
            "custody_manifest_may_not_bind_history_index": True,
            "unmodeled_preterminal_artifacts_may_contain_content_identities": False,
        },
        "control_evidence_validation_algorithm": {
            "baseline_before_equals_after_for_every_control": True,
            "control_count_equals_76": True,
            "control_ids_equal_exact_frozen_order": True,
            "control_row_expectations_equal_exact_frozen_v0_profiles": True,
            "observations_pass_and_isolation_fields_are_runtime_values": True,
            "direct_command_and_node_equal_frozen_values": True,
            "expected_and_observed_error_codes_must_match_for_passing_rows": True,
            "invented_equal_expected_and_observed_error_codes_are_rejected": True,
            "primary_readiness_runtime_partition_equals_51_7_18": True,
            "result_root_algorithm_id": (
                "LOOP_CONTROL_STAGE_A_76_CONTROL_RESULTS_ROOT_v1"
            ),
            "result_root_recomputed_from_canonical_rows": True,
            "row_pass_conjunction_equals_all_results_passed": True,
            "blocked_evidence_requires_at_least_one_failed_control_row": True,
            "every_row_baseline_equals_frozen_core_candidate_root": True,
        },
        "control_results_root_contract": {
            "algorithm_id": "LOOP_CONTROL_STAGE_A_76_CONTROL_RESULTS_ROOT_v1",
            "domain": "LOOP_CONTROL_STAGE_A_76_CONTROL_RESULTS_ROOT_v1",
            "row_order": "EXACT_FROZEN_76_CONTROL_PREFIX_ORDER",
            "row_payload": "ENTIRE_CLOSED_CONTROL_RESULT_OBJECT",
            "row_serializer": "COMPACT_CANONICAL_FINITE_JSON_UTF8",
            "root_preimage": (
                "UTF8_DOMAIN_NUL_PLUS_ROWS_JOINED_LF_NO_TERMINAL_LF"
            ),
            "control_evidence_execution_report_terminal_roots_must_be_equal": True,
            "all_three_roots_recomputed_from_actual_control_evidence_rows": True,
        },
        "control_count_consistency": {
            "blocked_status_requires_at_least_one_block_reason_code": True,
            "category_observed_counts_sum_to_total_observed": True,
            "category_passed_counts_sum_to_total_passed": True,
            "complete_status_requires_empty_block_reason_codes": True,
            "passed_is_at_most_observed_is_at_most_expected": True,
            "primary_readiness_runtime_expected_sum": "51_PLUS_7_PLUS_18_EQUALS_76",
        },
        "hidden_cycle_prohibitions": [
            "SOURCE_MANIFEST_MAY_NOT_FREEZE_ITS_OWN_FUTURE_SHA256",
            "IMPLEMENTATION_CODE_MAY_NOT_HARDCODE_FUTURE_SOURCE_MANIFEST_SHA256",
            "SUCCESSOR_CONTRACT_MAY_NOT_FREEZE_FUTURE_SOURCE_MANIFEST_SHA256",
            "CANDIDATE_TREE_MAY_NOT_INCLUDE_TRACE_OR_REPORT_THAT_EMBEDS_THAT_TREE_ROOT",
            "GENERATED_EVIDENCE_ARTIFACTS_MAY_NOT_EMBED_GENERATED_EVIDENCE_ROOT",
            "PROJECTION_AND_HISTORY_INDEX_MAY_NOT_BIND_EACH_OTHER",
            "CUSTODY_MANIFEST_AND_HISTORY_INDEX_MAY_NOT_BIND_EACH_OTHER",
            "FIXED_COMMAND_MAY_NOT_CONTAIN_FUTURE_SOURCE_MANIFEST_SHA256",
            "RUNTIME_MANIFEST_MAY_NOT_ASSERT_POSTTERMINAL_FILESYSTEM_STATE",
            "ROLLBACK_INVENTORY_MAY_LIST_FUTURE_PATHS_BUT_NOT_HASH_FUTURE_ARTIFACTS",
            "TERMINAL_ENVELOPE_MAY_NOT_CONTAIN_FUTURE_GIT_EVIDENCE_COMMIT",
            "NO_POSTTERMINAL_INTEGRATION_FILE_MAY_BE_ADDED_INSIDE_FINALIZED_RUN_ROOT",
            "SCHEMA_MAY_NOT_FREEZE_OUTPUT_HASH_PRODUCED_UNDER_THAT_SCHEMA",
        ],
        "inventory_algorithms": {
            "core_candidate_artifact_root": {
                "domain": "LOOP_CONTROL_STAGE_A_CANDIDATE_ARTIFACT_ROOT_v1",
                "row_fields": ["artifact_kind", "path", "sha256", "size_bytes"],
                "row_order": "UTF8_PATH_BYTE_ASCENDING",
                "row_serializer": "COMPACT_CANONICAL_FINITE_JSON_UTF8",
                "root_preimage": "UTF8_DOMAIN_NUL_PLUS_ROWS_JOINED_LF_NO_TERMINAL_LF",
                "unique_paths_required": True,
            },
            "generated_evidence_artifact_root": {
                "domain": "LOOP_CONTROL_STAGE_A_GENERATED_EVIDENCE_ROOT_v1",
                "row_fields": ["artifact_kind", "path", "sha256", "size_bytes"],
                "row_order": "UTF8_PATH_BYTE_ASCENDING",
                "row_serializer": "COMPACT_CANONICAL_FINITE_JSON_UTF8",
                "root_preimage": "UTF8_DOMAIN_NUL_PLUS_ROWS_JOINED_LF_NO_TERMINAL_LF",
                "unique_paths_required": True,
            },
            "preterminal_inventory_root": {
                "domain": "LOOP_CONTROL_STAGE_A_PRETERMINAL_INVENTORY_ROOT_v1",
                "exclusions": [
                    "TERMINAL_ENVELOPE_ITSELF",
                    "EXPLICITLY_REMOVED_TRANSIENT_RECONSTRUCTION_BYTES",
                ],
                "row_fields": ["phase", "artifact_kind", "path", "sha256", "size_bytes"],
                "row_order": "UTF8_PATH_BYTE_ASCENDING",
                "row_serializer": "COMPACT_CANONICAL_FINITE_JSON_UTF8",
                "root_preimage": "UTF8_DOMAIN_NUL_PLUS_ROWS_JOINED_LF_NO_TERMINAL_LF",
                "unique_paths_required": True,
            },
        },
        "runtime_path_contract": {
            "fixed_paths": {
                "control_evidence": "validation/LOOP_CONTROL_STAGE_A_CONTROL_EVIDENCE_v1.json",
                "consumer_source_map": "consumers/LOOP_CONTROL_REGISTRY_CONSUMER_SOURCE_MAP_v2.json",
                "custody_manifest": "custody/LOOP_CONTROL_LEGACY_BYTE_CUSTODY_MANIFEST_v1.json",
                "custody_payload": "custody/LOOP_CONTROL_LEGACY_BYTE_CUSTODY_v1.json.gz",
                "execution_preflight": "manifests/LOOP_CONTROL_EXECUTION_PREFLIGHT_v1.json",
                "execution_report": "validation/LOOP_CONTROL_STAGE_A_EXECUTION_REPORT_v2.json",
                "history_index": "history/LOOP_CONTROL_HISTORY_INDEX_v1.prototype.json",
                "projection": "projection/LOOP_CONTROL_CURRENT_v1.prototype.json",
                "reconstruction_result": "compat/LOOP_CONTROL_LEGACY_RECONSTRUCTION_RESULT_v1.json",
                "reviewed_trust_anchors": "authority/LOOP_CONTROL_REVIEWED_TRUST_ANCHORS_v1.json",
                "rollback_inventory": "manifests/LOOP_CONTROL_RUN_ROLLBACK_INVENTORY_v1.json",
                "runtime_manifest": "manifests/LOOP_CONTROL_READ_ONLY_PROTOTYPE_RUN_MANIFEST_v2.json",
                "runtime_trace": "traces/LOOP_CONTROL_RUNTIME_SHADOW_TRACE_v1.jsonl",
                "runtime_trace_manifest": "traces/LOOP_CONTROL_SHADOW_TRACE_MANIFEST_v1.json",
                "source_manifest": "manifests/LOOP_CONTROL_EXECUTION_SOURCE_MANIFEST_v2.json",
                "terminal_envelope": "manifests/LOOP_CONTROL_STAGE_A_TERMINAL_EXECUTION_ENVELOPE_v1.json",
                "validation_report": "validation/LOOP_CONTROL_REGISTRY_V1_VALIDATION_REPORT.json",
                "writer_probe": "validation/LOOP_CONTROL_WRITER_PROBE_v1.json",
            },
            "fixed_path_to_kind": {
                "authority/LOOP_CONTROL_REVIEWED_TRUST_ANCHORS_v1.json": "REVIEWED_TRUST_ANCHORS",
                "compat/LOOP_CONTROL_LEGACY_RECONSTRUCTION_RESULT_v1.json": "RECONSTRUCTION_RESULT",
                "consumers/LOOP_CONTROL_REGISTRY_CONSUMER_SOURCE_MAP_v2.json": "CONSUMER_SOURCE_MAP",
                "custody/LOOP_CONTROL_LEGACY_BYTE_CUSTODY_MANIFEST_v1.json": "CUSTODY_MANIFEST",
                "custody/LOOP_CONTROL_LEGACY_BYTE_CUSTODY_v1.json.gz": "CUSTODY_PAYLOAD",
                "history/LOOP_CONTROL_HISTORY_INDEX_v1.prototype.json": "HISTORY_INDEX",
                "manifests/LOOP_CONTROL_EXECUTION_PREFLIGHT_v1.json": "EXECUTION_PREFLIGHT",
                "manifests/LOOP_CONTROL_EXECUTION_SOURCE_MANIFEST_v2.json": "SOURCE_MANIFEST",
                "manifests/LOOP_CONTROL_READ_ONLY_PROTOTYPE_RUN_MANIFEST_v2.json": "RUNTIME_MANIFEST",
                "manifests/LOOP_CONTROL_RUN_ROLLBACK_INVENTORY_v1.json": "ROLLBACK_INVENTORY",
                "manifests/LOOP_CONTROL_STAGE_A_TERMINAL_EXECUTION_ENVELOPE_v1.json": "TERMINAL_ENVELOPE",
                "projection/LOOP_CONTROL_CURRENT_v1.prototype.json": "CURRENT_PROJECTION",
                "traces/LOOP_CONTROL_RUNTIME_SHADOW_TRACE_v1.jsonl": "RUNTIME_TRACE",
                "traces/LOOP_CONTROL_SHADOW_TRACE_MANIFEST_v1.json": "RUNTIME_TRACE_MANIFEST",
                "validation/LOOP_CONTROL_REGISTRY_V1_VALIDATION_REPORT.json": "VALIDATION_REPORT",
                "validation/LOOP_CONTROL_STAGE_A_CONTROL_EVIDENCE_v1.json": "CONTROL_EVIDENCE",
                "validation/LOOP_CONTROL_STAGE_A_EXECUTION_REPORT_v2.json": "EXECUTION_REPORT",
                "validation/LOOP_CONTROL_WRITER_PROBE_v1.json": "WRITER_PROBE",
            },
            "history_shard_pattern": (
                "^history/shards/LOOP_CONTROL_HISTORY_[0-9]{4}[.]jsonl$"
            ),
            "path_to_kind_is_closed_and_exact": True,
            "prototype_runtime_base": "formal/scratch/loop_control_registry_v1_prototype",
            "run_root_relation": "PROTOTYPE_RUNTIME_BASE_SLASH_VALIDATED_RUN_ID",
            "run_id_pattern": "^[A-Za-z0-9][A-Za-z0-9_-]{0,63}$",
        },
        "source_manifest_root_algorithms": {
            "allowed_output_specification": {
                "domain": "LOOP_CONTROL_STAGE_A_ALLOWED_OUTPUT_SPECIFICATION_ROOT_v1",
                "preimage": "COMPACT_CANONICAL_RUNTIME_PATH_CONTRACT_FROM_REVIEWED_SUCCESSOR_CONTRACT",
            },
            "implementation_tree": {
                "domain": "LOOP_CONTROL_STAGE_A_IMPLEMENTATION_TREE_ROOT_v1",
                "row_fields": [
                    "path",
                    "git_commit",
                    "git_blob",
                    "sha256",
                    "size_bytes",
                ],
                "row_order": "EXACT_AUTHORIZED_FOUR_PATH_ORDER",
                "row_serializer": "COMPACT_CANONICAL_FINITE_JSON_UTF8",
                "root_preimage": "UTF8_DOMAIN_NUL_PLUS_IMPLEMENTATION_COMMIT_NUL_PLUS_ROWS_JOINED_LF",
            },
            "input_inventory": {
                "domain": "LOOP_CONTROL_STAGE_A_SOURCE_INPUT_INVENTORY_ROOT_v1",
                "row_fields": [
                    "role",
                    "path",
                    "git_commit",
                    "git_blob",
                    "sha256",
                    "size_bytes",
                ],
                "row_order": "UTF8_ROLE_THEN_PATH_BYTE_ASCENDING",
                "row_serializer": "COMPACT_CANONICAL_FINITE_JSON_UTF8",
                "root_preimage": "UTF8_DOMAIN_NUL_PLUS_ROWS_JOINED_LF_NO_TERMINAL_LF",
            },
        },
        "independent_review_validation_algorithm": {
            "control_ids_and_error_codes_equal_exact_12_row_successor_contract": True,
            "execution_commit_and_terminal_blob_loaded_from_git": True,
            "fresh_baseline_per_mutation_required": True,
            "review_cannot_accept_without_terminal_envelope": True,
            "successor_result_root_recomputed": True,
            "terminal_and_execution_report_statuses_must_agree": True,
        },
        "historical_v0_blocked_preflight": {
            "candidate_artifacts_created": False,
            "classification": "blocked_preflight_contract_unsatisfiable",
            "controls_executed": 0,
            "controls_expected": 76,
            "error_code": V0_CYCLE_ERROR,
            "implementation_commit": SOURCE_COMMIT,
            "prototype_run_root_created": False,
            "source_registry_sha256": SOURCE_REGISTRY_SHA256,
            "stage_b_authorized": False,
            "v0_contract": bindings[V0_CONTRACT_REL],
            "v0_independent_review": bindings[V0_REVIEW_REL],
        },
        "implementation_path_contract": {
            "authorized_path_count": 4,
            "authorized_paths": AUTHORIZED_IMPLEMENTATION_PATHS,
            "baseline_at_blocked_v0_commit": {
                path: bindings[path] for path in AUTHORIZED_IMPLEMENTATION_PATHS
            },
            "future_v1_implementation_diff_may_touch_only_authorized_paths": True,
            "v0_blocked_implementation_commit_must_not_be_amended": True,
        },
        "path_safety_contract": {
            "maximum_relative_path_length": 240,
            "reject_absolute_drive_unc_or_slash_paths": True,
            "reject_control_or_windows_forbidden_characters": True,
            "reject_dot_segments_repeated_separators_or_trailing_dot_space": True,
            "reject_reserved_windows_device_names_case_insensitively": True,
            "resolved_path_must_remain_beneath_exact_run_root": True,
            "symlink_reparse_or_junction_escape_rejected": True,
        },
        "nonpromotion": {
            "consumer_cutover_performed": False,
            "current_projection_authoritative": False,
            "maintenance_target": MAINTENANCE_TARGET,
            "monolith_remains_authoritative_and_unchanged": True,
            "pillar_or_seam_claim_changed": False,
            "prototype_artifacts_created": False,
            "scientific_target": SCIENTIFIC_TARGET,
            "stage_a_execution_performed": False,
            "stage_b_authorized": False,
            "unit_ledger_executed": False,
        },
        "runtime_artifact_roles": {
            "execution_report": (
                "ADJUDICATES_ONLY_PRETERMINAL_76_CONTROL_EVIDENCE_AND_BINDS_RUNTIME"
            ),
            "independent_review": (
                "BINDS_TERMINAL_ENVELOPE_AND_REEXECUTES_SUCCESSOR_REGRESSIONS"
            ),
            "runtime_manifest": (
                "BINDS_SOURCE_MANIFEST_AND_FINALIZED_CANDIDATE_OUTPUTS_ONLY"
            ),
            "source_manifest": "BINDS_ONLY_FROZEN_AUTHORIZED_PREEXECUTION_INPUTS",
            "terminal_envelope": (
                "FINAL_ONE_WAY_CUSTODY_BINDING_FOR_RUNTIME_REPORT_AND_CANDIDATE"
            ),
        },
        "postterminal_control_storage": {
            "allowed_locations": [
                "IN_MEMORY_DURING_INDEPENDENT_REVIEW",
                "INSIDE_EXTERNAL_INDEPENDENT_REVIEW_ARTIFACT",
            ],
            "may_be_written_inside_finalized_run_root": False,
            "terminal_envelope_may_bind_postterminal_results": False,
        },
        "source_commit_layout": {
            "implementation_paths_present": {
                path: _git_path_exists(SOURCE_COMMIT, path)
                for path in AUTHORIZED_IMPLEMENTATION_PATHS
            },
            "production_and_prototype_paths_absent": {
                path: not _git_path_exists(SOURCE_COMMIT, path)
                for path in PRODUCTION_LAYOUT_PATHS
            },
        },
        "source_manifest_validation_algorithm": {
            "authorized_input_count": 10,
            "exact_role_path_map": SOURCE_INPUT_ROLE_PATHS,
            "each_role_occurs_exactly_once": True,
            "implementation_path_count": 4,
            "implementation_rows_loaded_from_git_not_candidate_values": True,
            "review_commit_and_blob_required_for_successor_review": True,
            "source_registry_identity_must_equal_external_frozen_identity": True,
        },
        "cross_document_validation_algorithm": {
            "all_run_ids_equal": True,
            "all_source_manifest_identities_equal_actual_bytes": True,
            "complete_status_requires_exactly_76_observed_and_passed": True,
            "control_evidence_execution_report_terminal_result_roots_equal": True,
            "control_result_root_algorithm_ids_equal_frozen_value": True,
            "execution_report_must_bind_actual_runtime_manifest_bytes": True,
            "runtime_manifest_must_bind_actual_source_manifest_bytes": True,
            "terminal_must_bind_actual_runtime_and_report_bytes": True,
            "blocked_status_cannot_claim_all_controls_passed": True,
            "direct_invocation_command_node_exit_and_output_digests_equal_across_documents": True,
            "complete_status_requires_direct_invocation_exit_zero": True,
            "core_candidate_and_generated_evidence_roots_are_distinct": True,
        },
        "runtime_schemas": schemas,
        "schema_id": (
            "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_"
            "CONTRACT_BUNDLE_20260711_v1"
        ),
        "source_commit": SOURCE_COMMIT,
        "stage_a_control_contract": {
            "existing_preterminal_control_count": 76,
            "existing_preterminal_control_count_changed": False,
            "primary_control_count": 51,
            "readiness_control_count": 7,
            "runtime_contract_control_count": 18,
            "exact_control_ids": stage_a_ids,
            "exact_control_id_root_sha256": sha256(
                "\n".join(stage_a_ids).encode("utf-8")
            ),
            "exact_control_profiles": stage_a_profiles,
            "exact_control_profile_count": 76,
            "exact_control_profile_root_algorithm": {
                "domain": (
                    "LOOP_CONTROL_STAGE_A_V0_IMMUTABLE_CONTROL_PROFILE_ROOT_v1"
                ),
                "row_order": "EXACT_FROZEN_76_CONTROL_PREFIX_ORDER",
                "row_serializer": "COMPACT_CANONICAL_FINITE_JSON_UTF8",
                "root_preimage": (
                    "UTF8_DOMAIN_NUL_PLUS_ROWS_JOINED_LF_NO_TERMINAL_LF"
                ),
            },
            "exact_control_profile_root_sha256": _control_profile_root(
                stage_a_profiles
            ),
            "successor_regression_control_count": 12,
            "successor_regressions_are_inside_preterminal_execution_report": False,
            "successor_regressions_run_during_packet_and_independent_review": True,
            "successor_regressions_may_create_report_terminal_cycle": False,
            "successor_regression_results": controls,
            "successor_regression_results_root_sha256": _control_root(controls),
        },
        "status": (
            "ONE_WAY_STAGE_A_EXECUTION_SUCCESSOR_CONTRACT_PREPARED_"
            "INDEPENDENT_REVIEW_REQUIRED_NO_PROTOTYPE_EXECUTION_OR_AUTHORITY_CHANGE"
        ),
        "supersession": {
            "effective_only_after_independent_review": True,
            "preserves_v0_packet_contract_review_and_blocked_implementation": True,
            "reason": "REMOVE_RECIPROCAL_SOURCE_MANIFEST_RUNTIME_MANIFEST_HASH_CYCLE",
            "supersedes_contract": bindings[V0_CONTRACT_REL],
            "supersedes_only_for_future_stage_a_execution": True,
        },
        "terminal_envelope_contract": {
            "binds": [
                "SOURCE_MANIFEST_IDENTITY",
                "RUNTIME_MANIFEST_IDENTITY",
                "EXECUTION_REPORT_IDENTITY",
                "CONTROL_EVIDENCE_IDENTITY",
                "COMPLETE_CANDIDATE_ARTIFACT_SET_AND_ROOT",
                "SOURCE_REGISTRY_HASH",
                "RUN_ID_AND_CANDIDATE_STATUS",
            ],
            "candidate_coverage_must_equal_runtime_manifest_coverage": True,
            "earlier_artifacts_may_bind_terminal_envelope": False,
            "self_hash_field_allowed": False,
            "stage_a_review_requires_terminal_envelope": True,
        },
        "terminal_validation_algorithm": {
            "candidate_artifact_count_equals_array_length": True,
            "candidate_shard_count_equals_history_shard_rows": True,
            "candidate_rows_equal_runtime_manifest_rows_byte_for_byte": True,
            "core_candidate_inventory_excludes_all_generated_evidence": True,
            "evidence_artifact_count_equals_array_length": True,
            "evidence_rows_equal_runtime_manifest_rows_byte_for_byte": True,
            "explicit_identities_equal_corresponding_preterminal_rows": True,
            "finalized_run_root_contains_no_uninventoried_regular_file": True,
            "no_file_may_be_added_inside_run_root_after_terminal_creation": True,
            "preterminal_artifact_count_equals_array_length": True,
            "recompute_all_hashes_sizes_and_roots_from_actual_bytes": True,
            "unique_paths_required_across_each_inventory": True,
        },
    }


def build_packet() -> dict[str, Any]:
    contract_raw = canonical_json_bytes(build_contract())
    return {
        "authorization": {
            "implementation_change_authorized": False,
            "independent_review_required": True,
            "maintenance_target_rotation_authorized": False,
            "prototype_execution_authorized": False,
            "registry_cutover_authorized": False,
            "registry_migration_execution_authorized": False,
            "scientific_target_rotation_authorized": False,
            "stage_b_authorized": False,
            "unit_ledger_execution_authorized": False,
        },
        "boundary": {
            "candidate_artifacts_created": False,
            "consumer_migration_started": False,
            "legacy_monolith_modified_or_retired": False,
            "one_way_contract_prepared_only": True,
            "prototype_execution_attempted": False,
            "scientific_artifacts_or_claims_changed": False,
            "terminal_execution_envelope_created": False,
            "v0_implementation_amended": False,
        },
        "captured_at_utc": CAPTURED_AT_UTC,
        "contract_bundle": {
            "path": CONTRACT_REL,
            "sha256": sha256(contract_raw),
        },
        "counts": {
            "authorized_implementation_path_count": 4,
            "existing_stage_a_control_count": 76,
            "runtime_schema_count": 7,
            "successor_regression_control_count": 12,
        },
        "execution_target_recommended_not_selected": EXECUTION_TARGET,
        "maintenance_target": MAINTENANCE_TARGET,
        "packet_id": (
            "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_"
            "PACKET_20260711_v1"
        ),
        "packet_target": PACKET_TARGET,
        "review_target_recommended_not_selected": REVIEW_TARGET,
        "scientific_target": SCIENTIFIC_TARGET,
        "source_commit": SOURCE_COMMIT,
        "status": (
            "ONE_WAY_STAGE_A_EXECUTION_SUCCESSOR_PACKET_PREPARED_"
            "INDEPENDENT_REVIEW_REQUIRED_NO_EXECUTION_MIGRATION_CUTOVER_OR_SCIENCE"
        ),
        "v0_blocked_preflight": {
            "classification": "blocked_preflight_contract_unsatisfiable",
            "error_code": V0_CYCLE_ERROR,
            "implementation_commit": SOURCE_COMMIT,
            "source_registry_sha256": SOURCE_REGISTRY_SHA256,
        },
    }


def build_all() -> dict[Path, bytes]:
    contract = canonical_json_bytes(build_contract())
    packet = canonical_json_bytes(build_packet())
    return {CONTRACT_PATH: contract, PACKET_PATH: packet}


def _atomic_write(path: Path, raw: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        dir=path.parent,
        prefix=f".{path.name}.",
        suffix=".tmp",
        delete=False,
    ) as handle:
        temporary = Path(handle.name)
        handle.write(raw)
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(temporary, path)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    outputs = build_all()
    if args.write:
        for path, raw in outputs.items():
            _atomic_write(path, raw)
        return 0
    mismatches = [
        path.relative_to(REPO_ROOT).as_posix()
        for path, raw in outputs.items()
        if not path.exists() or path.read_bytes() != raw
    ]
    if mismatches:
        raise SuccessorPreparationError(
            "generated successor artifacts differ: " + ", ".join(mismatches)
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
