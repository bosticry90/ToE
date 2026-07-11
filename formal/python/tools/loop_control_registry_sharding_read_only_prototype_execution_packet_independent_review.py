from __future__ import annotations

import argparse
import ast
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from typing import Any

from jsonschema.validators import validator_for

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SOURCE_COMMIT = "0261ec32029535e70f19587ed2f2755bb0bb9f22"
ORIGINAL_TRANSITION_SOURCE_COMMIT = "6e4d1e11b1953b9712588464b31c12047555189c"

PACKET_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_PACKET_"
    "20260711_v0.json"
)
CONTRACT_REL = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_CONTRACT_"
    "BUNDLE_20260711_v0.json"
)
GENERATOR_REL = (
    "formal/python/tools/"
    "loop_control_registry_sharding_read_only_prototype_execution_packet.py"
)
TEST_REL = (
    "formal/python/tests/"
    "test_loop_control_registry_sharding_read_only_prototype_execution_packet.py"
)
LEAN_REL = (
    "formal/toe_formal/ToeFormal/Release/"
    "LoopControlRegistryShardingReadOnlyPrototypeExecutionPacket.lean"
)
REGISTRY_REL = "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
MAINTENANCE_REL = "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v0.json"
AUTHORITY_REL = "formal/docs/release/CURRENT_AUTHORITATIVE_SURFACES_v0.md"
READINESS_REL = "formal/docs/release/SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0.json"
CONSUMER_REL = (
    "formal/docs/release/LOOP_CONTROL_REGISTRY_CONSUMER_SOURCE_MAP_20260711_v1.json"
)
REQUIREMENTS_REL = "requirements.ci.lock"
MANIFEST_REL = "formal/docs/release/GOVERNANCE_TEST_MANIFEST_v1.json"

OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_PACKET_"
    "INDEPENDENT_REVIEW_20260711_v0.json"
)

EXPECTED_SHA256 = {
    PACKET_REL: "661655d3a6ba8f77b75652f45e1709275f0c0ae372b87a18a868316502a76168",
    CONTRACT_REL: "272279d414591b25b3a519d22d92659f4a662ce1c9cbd5fadf3067f1eaa8f0bb",
    GENERATOR_REL: "aa3e1323b2cad2de4b97b369ad7583b65c79692dc5e66f437e427a34ae02f443",
    TEST_REL: "094e4814172c3ff92fb762233f37cbe4ccc837508ebc8e8a35a3ac78a6f72402",
    LEAN_REL: "1ec96cd56b9cd2cca062d96180d246b832d8c8719da587636f4a9729ce6c2249",
    REGISTRY_REL: "eda451133e8bbfe1ba0e815b29735f874e8b33e61d7fc5085999c4ba38df0543",
    MAINTENANCE_REL: "ada2c9c9c4622c64f0ab0fb7033b8e39b790d55a29ee492dd03fea06afc3695b",
    AUTHORITY_REL: "cca3e7cb1855919bae8e5f189f04eb485bf2e2529aaff5e22c2a06e48b316248",
    READINESS_REL: "6a4273b3f95bca657bbc9dcdbab82d118a8223ab6de55a213374421b560838a1",
    CONSUMER_REL: "5592a666adf8cf2ee70d4ab661001cf7d386caa79c3d7a7df7e9f5ac242fb642",
    REQUIREMENTS_REL: "79c5d6ca6995338c20fdf4c7bdb2748746cbef0e226de1c55489ddb25658b47b",
    MANIFEST_REL: "0f5bd56ef5b875f36e1d964b69747dd265273063281b15ff1da81ff9e2715161",
}

EXPECTED_GIT_BLOBS = {
    PACKET_REL: "a77882a8d601662411bf33ab8b93e9153eb7fe1c",
    CONTRACT_REL: "abf0d597c05342a37a31db5e166dd2b5531cb888",
    GENERATOR_REL: "3988b67e6efd793840d9da2856e58755fa1ad08c",
    TEST_REL: "62fe9fce6abe84c64e4f172d3bdd7f25a7926269",
    LEAN_REL: "a7e6078d4ed788e18bfd34222509dd436d43e609",
    REGISTRY_REL: "e6c5b3773dccd92fde9c0a8d486a56f993d6b235",
    MAINTENANCE_REL: "dca311d6abe38a872495c07f302d13ad886c0232",
    AUTHORITY_REL: "d46c5fb1966dcefc6b923776b7d94c4f5009b889",
    READINESS_REL: "85711a7c8cb0bc6a1f77d85cf3873726a5d6aa22",
    CONSUMER_REL: "9f9846ba735813c5b2b18f7a0115d88230a36600",
    REQUIREMENTS_REL: "bcc393883b90739408ed14d53d57dd0b42d0c2bd",
    MANIFEST_REL: "9a9c7ac4a32b7ac48bf6a0bcca848366cddcbbaf",
}

EXPECTED_SIZE_BYTES = {
    PACKET_REL: 3313,
    CONTRACT_REL: 392459,
    GENERATOR_REL: 78289,
    TEST_REL: 47815,
    LEAN_REL: 4106,
    REGISTRY_REL: 52340650,
    MAINTENANCE_REL: 1768,
    AUTHORITY_REL: 714575,
    READINESS_REL: 79556,
    CONSUMER_REL: 469583,
    REQUIREMENTS_REL: 741,
    MANIFEST_REL: 43317,
}

SCIENTIFIC_TARGET = "execute_pillar_seam_unit_mapping_ledger_v0"
MAINTENANCE_TARGET = (
    "prepare_loop_control_registry_sharding_and_current_projection_packet_v0"
)
EXECUTION_TARGET = "execute_loop_control_registry_sharding_read_only_prototype_v0"

FORBIDDEN_PATHS = [
    "formal/docs/release/loop_control/LOOP_CONTROL_CURRENT_v1.json",
    "formal/docs/release/loop_control/LOOP_CONTROL_HISTORY_INDEX_v1.json",
    "formal/docs/release/loop_control/shards",
    "formal/docs/release/loop_control/LOOP_CONTROL_LEGACY_BYTE_CUSTODY_v1.json.gz",
    "formal/python/toe/loop_control_registry_v1.py",
    "formal/python/toe/loop_control_registry_v1_validator.py",
    "formal/scratch/loop_control_registry_v1_prototype",
]

TRANSITION_PATHS = [
    "formal/python/tools/loop_control_registry_sharding_execution_readiness_packet.py",
    "formal/python/tools/loop_control_registry_sharding_execution_readiness_packet_v1.py",
    "formal/python/tools/loop_control_registry_sharding_execution_readiness_packet_v2.py",
    "formal/python/tools/loop_control_registry_sharding_execution_readiness_packet_v3.py",
    "formal/python/tools/loop_control_registry_sharding_execution_readiness_packet_v3_independent_review.py",
    "formal/python/tests/test_loop_control_registry_sharding_execution_readiness_packet.py",
    "formal/python/tests/test_loop_control_registry_sharding_execution_readiness_packet_v1.py",
    "formal/python/tests/test_loop_control_registry_sharding_execution_readiness_packet_v2.py",
    "formal/python/tests/test_loop_control_registry_sharding_execution_readiness_packet_v3.py",
    "formal/python/tests/test_loop_control_registry_sharding_execution_readiness_packet_v3_independent_review.py",
]

TRANSITION_BOUNDARIES = {
    TRANSITION_PATHS[0]: "a0d44da40922d6547f02241174fa640edb3f9fa8",
    TRANSITION_PATHS[5]: "a0d44da40922d6547f02241174fa640edb3f9fa8",
    TRANSITION_PATHS[1]: "e2af09bbb4355604eee4566707afd3407ed6c4b9",
    TRANSITION_PATHS[6]: "e2af09bbb4355604eee4566707afd3407ed6c4b9",
    TRANSITION_PATHS[2]: "20a57192305cc794397fdcef06f54cab30c37205",
    TRANSITION_PATHS[7]: "20a57192305cc794397fdcef06f54cab30c37205",
    TRANSITION_PATHS[3]: "f9051af27988dd745bf39d28ae4d610973d5a029",
    TRANSITION_PATHS[8]: "f9051af27988dd745bf39d28ae4d610973d5a029",
    TRANSITION_PATHS[4]: "6e4d1e11b1953b9712588464b31c12047555189c",
    TRANSITION_PATHS[9]: "6e4d1e11b1953b9712588464b31c12047555189c",
}


class IndependentReviewError(ValueError):
    pass


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def canonical_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False, allow_nan=False)
        + "\n"
    ).encode("utf-8")


def _git_blob(relative: str, commit: str = SOURCE_COMMIT) -> bytes:
    result = subprocess.run(
        ["git", "show", f"{commit}:{relative}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        raise IndependentReviewError(f"missing reviewed blob: {commit}:{relative}")
    return result.stdout


def _git_blob_oid(relative: str, commit: str = SOURCE_COMMIT) -> str:
    result = subprocess.run(
        ["git", "rev-parse", f"{commit}:{relative}"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    return result.stdout.strip()


def _path_exists_at_commit(relative: str, commit: str) -> bool:
    return (
        subprocess.run(
            ["git", "cat-file", "-e", f"{commit}:{relative}"],
            cwd=REPO_ROOT,
            capture_output=True,
            check=False,
        ).returncode
        == 0
    )


def _strict_json(raw: bytes) -> Any:
    def pairs_hook(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        output: dict[str, Any] = {}
        for key, value in pairs:
            if key in output:
                raise IndependentReviewError(f"duplicate JSON key: {key}")
            output[key] = value
        return output

    def reject_constant(value: str) -> Any:
        raise IndependentReviewError(f"nonfinite JSON constant: {value}")

    return json.loads(raw, object_pairs_hook=pairs_hook, parse_constant=reject_constant)


def _assert_closed(node: Any, pointer: str = "$") -> None:
    if isinstance(node, dict):
        if node.get("type") == "object":
            if node.get("additionalProperties") is not False:
                raise IndependentReviewError(f"open object schema: {pointer}")
            if set(node.get("required", [])) != set(node.get("properties", {})):
                raise IndependentReviewError(f"required/property drift: {pointer}")
        for key, value in node.items():
            _assert_closed(value, f"{pointer}/{key}")
    elif isinstance(node, list):
        for index, value in enumerate(node):
            _assert_closed(value, f"{pointer}/{index}")


def _reviewed_inputs() -> dict[str, Any]:
    output: dict[str, Any] = {}
    for relative, expected_sha in EXPECTED_SHA256.items():
        raw = _git_blob(relative)
        observed = {
            "git_blob": _git_blob_oid(relative),
            "path": relative,
            "sha256": _sha256(raw),
            "size_bytes": len(raw),
        }
        expected = {
            "git_blob": EXPECTED_GIT_BLOBS[relative],
            "path": relative,
            "sha256": expected_sha,
            "size_bytes": EXPECTED_SIZE_BYTES[relative],
        }
        if observed != expected:
            raise IndependentReviewError(f"reviewed input drift: {relative}")
        output[relative] = observed
    return output


_FOCUSED_CACHE: dict[str, Any] | None = None


def _focused_validation() -> dict[str, Any]:
    global _FOCUSED_CACHE
    if _FOCUSED_CACHE is not None:
        return dict(_FOCUSED_CACHE)
    tree = ast.parse(_git_blob(TEST_REL), filename=TEST_REL)
    discovered = sum(
        isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        and node.name.startswith("test_")
        for node in tree.body
    )
    if discovered != 23:
        raise IndependentReviewError("focused test discovery count drift")
    command = [sys.executable, "-m", "pytest", "-q", TEST_REL]
    with tempfile.TemporaryDirectory(
        prefix="toe-registry-packet-review-"
    ) as temporary_directory:
        checkout = Path(temporary_directory) / "reviewed-tree"
        add = subprocess.run(
            [
                "git",
                "worktree",
                "add",
                "--detach",
                "--force",
                str(checkout),
                SOURCE_COMMIT,
            ],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            timeout=180,
            check=False,
        )
        if add.returncode != 0:
            raise IndependentReviewError(
                f"could not create reviewed detached worktree: {add.stderr.strip()}"
            )
        try:
            result = subprocess.run(
                command,
                cwd=checkout,
                capture_output=True,
                text=True,
                timeout=180,
                check=False,
                env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
            )
        finally:
            remove = subprocess.run(
                ["git", "worktree", "remove", "--force", str(checkout)],
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                timeout=180,
                check=False,
            )
            if remove.returncode != 0:
                subprocess.run(
                    ["git", "worktree", "prune"],
                    cwd=REPO_ROOT,
                    capture_output=True,
                    text=True,
                    timeout=60,
                    check=False,
                )
                raise IndependentReviewError(
                    f"could not remove reviewed detached worktree: {remove.stderr.strip()}"
                )
    combined = f"{result.stdout}\n{result.stderr}"
    matched = re.search(r"(?:^|\s)(\d+) passed(?:\s|$)", combined)
    passed = int(matched.group(1)) if matched else 0
    if result.returncode != 0 or passed != 23:
        raise IndependentReviewError(
            f"focused validation failed: returncode={result.returncode}, passed={passed}"
        )
    _FOCUSED_CACHE = {
        "command": ".\\py.ps1 -m pytest -q " + TEST_REL,
        "discovered_test_count": 23,
        "failed_test_count": 0,
        "passed_test_count": 23,
        "result": "PASS",
        "test_path": TEST_REL,
    }
    return dict(_FOCUSED_CACHE)


def _probe() -> dict[str, Any]:
    reviewed = _reviewed_inputs()
    packet = _strict_json(_git_blob(PACKET_REL))
    contract = _strict_json(_git_blob(CONTRACT_REL))
    maintenance = _strict_json(_git_blob(MAINTENANCE_REL))
    manifest = _strict_json(_git_blob(MANIFEST_REL))

    if packet["contract_bundle"]["sha256"] != EXPECTED_SHA256[CONTRACT_REL]:
        raise IndependentReviewError("packet/contract cross-hash drift")
    if packet["scientific_target"] != SCIENTIFIC_TARGET:
        raise IndependentReviewError("packet scientific target drift")
    if packet["maintenance_target"] != MAINTENANCE_TARGET:
        raise IndependentReviewError("packet maintenance target drift")
    if packet["execution_target_recommended_not_selected"] != EXECUTION_TARGET:
        raise IndependentReviewError("execution target drift")
    if packet["authorization"]["independent_review_required"] is not True:
        raise IndependentReviewError("packet no longer requires review")
    if any(
        value is not False
        for key, value in packet["authorization"].items()
        if key != "independent_review_required"
    ) or any(value is not False for value in packet["boundary"].values()):
        raise IndependentReviewError("preparation packet self-authorizes or overclaims")
    if contract["authorization"]["contract_independent_review_required"] is not True:
        raise IndependentReviewError("contract no longer requires review")
    if any(
        value is not False
        for key, value in contract["authorization"].items()
        if key != "contract_independent_review_required"
    ):
        raise IndependentReviewError("preparation contract self-authorizes")

    counts = packet["counts"]
    expected_counts = {
        "future_stage_b_total_control_count": 78,
        "historical_absence_gate_count": 9,
        "primary_control_count": 52,
        "readiness_control_count": 8,
        "runtime_schema_count": 10,
        "stage_a_distinct_control_count": 58,
        "stage_a_runtime_contract_control_count": 18,
        "stage_a_total_control_count": 76,
        "stage_b_distinct_control_count": 60,
    }
    if counts != expected_counts:
        raise IndependentReviewError("packet count drift")

    schemas = contract["runtime_schemas"]
    if contract["runtime_schema_count"] != 10 or len(schemas) != 10:
        raise IndependentReviewError("runtime schema count drift")
    for name, schema in schemas.items():
        validator_for(schema).check_schema(schema)
        _assert_closed(schema, name)
    runtime = contract["runtime_validator_contract"]
    if (
        runtime["entrypoint_count"] != 11
        or runtime["negative_control_count"] != 18
        or runtime["execution_complete"] is not False
    ):
        raise IndependentReviewError("runtime validator contract drift")

    lifecycle = contract["lifecycle"]
    stage_a = lifecycle["stage_a_precutover_execution_after_separate_authorization"]
    excluded = ["REGISTRY-V1-NC-044", "REGISTRY-READINESS-V1-RC-001"]
    if (
        stage_a["distinct_control_count"] != 58
        or stage_a["runtime_contract_control_count"] != 18
        or stage_a["total_stage_a_control_count"] != 76
        or stage_a["cutover_control_ids_excluded"] != excluded
        or stage_a["final_all_controls_passed_harness_report_allowed"] is not False
    ):
        raise IndependentReviewError("Stage-A scope drift")
    stage_b = lifecycle["stage_b_full_harness_deferred_obligation"]
    if (
        stage_b["authorized_or_executable_under_this_contract"] is not False
        or stage_b["versioned_successor_packet_and_independent_review_required"] is not True
        or stage_b["future_total_control_count"] != 78
    ):
        raise IndependentReviewError("Stage-B deferral drift")
    anchor_authorization = schemas["reviewed_trust_anchors"]["properties"][
        "prototype_execution_authorization"
    ]["properties"]
    if (
        anchor_authorization["bounded_stage_a_authorized"]["const"] is not True
        or anchor_authorization["stage_b_authorized"]["const"] is not False
    ):
        raise IndependentReviewError("review anchor authorization schema drift")
    candidate = contract["artifact_source_and_candidate_tree_contract"]
    if (
        candidate["candidate_provided_roots_are_recomputed_not_trusted"] is not True
        or candidate[
            "candidate_supplied_artifact_kind_or_candidate_payload_flag_is_not_trusted"
        ]
        is not True
        or candidate["stage_b_candidate_comparison_semantics_deferred_to_versioned_successor"]
        is not True
    ):
        raise IndependentReviewError("candidate external-root boundary drift")

    transition = contract["historical_gate_executable_transition"]
    if (
        transition["affected_executable_checks"] != TRANSITION_PATHS
        or transition["per_check_historical_boundary"] != TRANSITION_BOUNDARIES
        or transition["performed_as_mechanical_change_in_this_preparation_tranche"]
        is not True
    ):
        raise IndependentReviewError("historical executable transition drift")
    original_bindings = contract["historical_absence_transition"][
        "affected_check_source_bindings"
    ]
    if set(original_bindings) != set(TRANSITION_PATHS):
        raise IndependentReviewError("historical source binding coverage drift")
    for relative in TRANSITION_PATHS:
        original = _git_blob(relative, ORIGINAL_TRANSITION_SOURCE_COMMIT)
        if original_bindings[relative] != {
            "git_blob": _git_blob_oid(relative, ORIGINAL_TRANSITION_SOURCE_COMMIT),
            "sha256": _sha256(original),
            "size_bytes": len(original),
        }:
            raise IndependentReviewError(f"historical source binding drift: {relative}")
        current = _git_blob(relative).decode("utf-8")
        if "(REPO_ROOT / relative).exists()" in current:
            raise IndependentReviewError(f"current-worktree absence check remains: {relative}")
    for relative, boundary in TRANSITION_BOUNDARIES.items():
        if "/tools/" in relative and boundary not in _git_blob(relative).decode("utf-8"):
            raise IndependentReviewError(f"historical boundary not embedded: {relative}")
    if any(_path_exists_at_commit(relative, SOURCE_COMMIT) for relative in FORBIDDEN_PATHS):
        raise IndependentReviewError("prototype or production path exists at reviewed commit")

    if maintenance["scientific_authority"]["current_target"] != SCIENTIFIC_TARGET:
        raise IndependentReviewError("maintenance scientific mirror drift")
    if maintenance["current_maintenance_target"] != MAINTENANCE_TARGET:
        raise IndependentReviewError("maintenance target drift")
    if manifest["test_tiers"].get(TEST_REL) != "TIER_INTEGRITY":
        raise IndependentReviewError("focused test is not integrity-enrolled")
    lean = _git_blob(LEAN_REL).decode("utf-8")
    for token in (
        EXPECTED_SHA256[PACKET_REL],
        EXPECTED_SHA256[CONTRACT_REL],
        "def stageATotalControlCount : Nat := 76",
        "def stageBExecutable : Bool := false",
    ):
        if token not in lean:
            raise IndependentReviewError(f"Lean certificate binding missing: {token}")

    implementation_paths = contract["execution_preflight_contract"][
        "implementation_source_manifest_paths"
    ]
    expected_implementation_paths = [
        "formal/python/tools/loop_control_registry_sharding_read_only_prototype_execution.py",
        "formal/python/toe/loop_control_registry_v1.py",
        "formal/python/toe/loop_control_registry_v1_validator.py",
        "formal/python/tests/test_loop_control_registry_v1_production_controls.py",
    ]
    if implementation_paths != expected_implementation_paths:
        raise IndependentReviewError("clean implementation path allowlist drift")
    if contract["allowed_and_prohibited_paths"][
        "future_tracked_implementation_paths_after_separate_authorization"
    ] != expected_implementation_paths:
        raise IndependentReviewError("future implementation path allowlist drift")

    return {
        "external_root_review": {
            "candidate_internal_values_authoritative": False,
            "contract_bundle_sha256": EXPECTED_SHA256[CONTRACT_REL],
            "packet_sha256": EXPECTED_SHA256[PACKET_REL],
            "reviewed_registry_sha256": EXPECTED_SHA256[REGISTRY_REL],
            "reviewed_requirements_sha256": EXPECTED_SHA256[REQUIREMENTS_REL],
            "trust_anchors_must_be_loaded_from_git_review": True,
        },
        "focused_validation": _focused_validation(),
        "historical_transition_review": {
            "forbidden_paths_absent_at_reviewed_commit": list(FORBIDDEN_PATHS),
            "historical_absence_gate_count": 9,
            "mechanically_transitioned_check_count": 10,
            "per_check_boundaries_verified": True,
            "production_or_prototype_paths_present": 0,
        },
        "implementation_integration_condition_review": {
            "authorization_is_conditional_on_execution_evidence": True,
            "authorized_clean_implementation_path_count": 4,
            "authorized_clean_implementation_paths": contract[
                "execution_preflight_contract"
            ]["implementation_source_manifest_paths"],
            "clean_implementation_commit_path_allowlist_expansion_authorized": False,
            "documentation_integration_allowed_in_clean_implementation_commit": False,
            "gitattributes_integration_allowed_in_clean_implementation_commit": False,
            "governance_manifest_enrollment_required_before_preflight": False,
            "governance_manifest_integration_allowed_in_clean_implementation_commit": False,
            "lean_integration_allowed_in_clean_implementation_commit": False,
            "post_execution_integration_deferred_to": (
                "INDEPENDENT_STAGE_A_REVIEW_OR_VERSIONED_SUCCESSOR"
            ),
            "production_control_test_direct_invocation_must_be_recorded_in_execution_evidence": True,
            "production_control_test_must_be_invoked_directly_by_execution_orchestrator": True,
            "production_control_test_path": (
                "formal/python/tests/test_loop_control_registry_v1_production_controls.py"
            ),
        },
        "protected_state_review": {
            "authority_surface_sha256": EXPECTED_SHA256[AUTHORITY_REL],
            "maintenance_authority_sha256": EXPECTED_SHA256[MAINTENANCE_REL],
            "readiness_surface_sha256": EXPECTED_SHA256[READINESS_REL],
            "registry_sha256": EXPECTED_SHA256[REGISTRY_REL],
            "scientific_target": SCIENTIFIC_TARGET,
            "maintenance_target": MAINTENANCE_TARGET,
            "protected_hashes_unchanged": True,
        },
        "reviewed_inputs": reviewed,
        "schema_and_runtime_contract_review": {
            "all_schemas_closed": True,
            "authorized_stage_a_total_control_count": 76,
            "deferred_stage_b_inherited_control_count": 60,
            "deferred_stage_b_total_control_count": 78,
            "excluded_cutover_control_ids": excluded,
            "inherited_stage_a_control_count": 58,
            "runtime_negative_control_count": 18,
            "runtime_schema_count": 10,
            "runtime_validator_entrypoint_count": 11,
            "stage_a_runtime_control_count": 18,
            "stage_b_requires_successor": True,
        },
    }


def build_review() -> dict[str, Any]:
    evidence = _probe()
    return {
        "authorization": {
            "authority_cutover_authorized": False,
            "bounded_read_only_prototype_implementation_authorized": True,
            "bounded_stage_a_authorization_conditional_on_execution_evidence": True,
            "bounded_stage_a_read_only_prototype_execution_authorized": True,
            "clean_implementation_commit_path_allowlist_expansion_authorized": False,
            "consumer_migration_authorized": False,
            "execution_target": EXECUTION_TARGET,
            "execution_target_selected_in_current_authority": False,
            "legacy_monolith_modification_or_retirement_authorized": False,
            "maintenance_target": MAINTENANCE_TARGET,
            "maintenance_target_rotation_authorized": False,
            "new_api_writes_authorized": False,
            "registry_cutover_authorized": False,
            "registry_migration_execution_authorized": False,
            "release_or_publication_authorized": False,
            "scientific_claim_or_blocker_movement_authorized": False,
            "scientific_target": SCIENTIFIC_TARGET,
            "scientific_target_rotation_authorized": False,
            "stage_a_76_control_harness_execution_authorized": True,
            "stage_b_full_harness_authorized": False,
            "unit_ledger_execution_authorized": False,
        },
        "boundary": {
            "consumer_cutover": False,
            "legacy_monolith_modification_or_retirement": False,
            "production_registry_migration": False,
            "prototype_implementation_or_output_created_by_review": False,
            "scientific_artifact_or_claim_change": False,
            "stage_b_execution": False,
            "target_or_authority_rotation": False,
        },
        "captured_at_utc": "2026-07-11T00:00:00Z",
        "decision": (
            "ACCEPT_PREPARATION_AND_AUTHORIZE_ONLY_BOUNDED_STAGE_A_76_CONTROL_"
            "READ_ONLY_PROTOTYPE_IMPLEMENTATION_AND_EXECUTION"
        ),
        **evidence,
        "independent_findings": [
            {
                "finding_id": "REGISTRY-READ-ONLY-PROTOTYPE-REVIEW-001",
                "status": "CLOSED_FOR_BOUNDED_STAGE_A_EXECUTION",
                "summary": (
                    "Committed preparation packet, contract, generator, 23-test suite, Lean certificate, "
                    "external roots, protected hashes, and the exact Stage-A 76-control "
                    "burden reproduce at the reviewed commit."
                ),
            },
            {
                "finding_id": "REGISTRY-READ-ONLY-PROTOTYPE-REVIEW-002",
                "status": "CLOSED_FOR_BOUNDED_STAGE_A_EXECUTION",
                "summary": (
                    "Ten historical absence checks now use exact committed boundaries, while "
                    "production authority paths and prototype outputs remain absent."
                ),
            },
            {
                "finding_id": "REGISTRY-READ-ONLY-PROTOTYPE-REVIEW-003",
                "status": "OPEN_DEFERRED_STAGE_B_AND_MIGRATION_OBLIGATION",
                "summary": (
                    "Stage B, consumer migration, registry cutover, monolith retirement, and "
                    "all scientific or authority effects remain unauthorized."
                ),
            },
            {
                "finding_id": "REGISTRY-READ-ONLY-PROTOTYPE-REVIEW-004",
                "status": "CONDITIONAL_STAGE_A_INTEGRATION_OBLIGATION",
                "summary": (
                    "The production-control test must be invoked directly by the Stage-A "
                    "execution orchestrator and recorded in execution evidence. Governance "
                    "manifest, .gitattributes, documentation, and Lean integration are "
                    "deferred to post-execution independent review or a versioned successor "
                    "and may not broaden the four-path clean implementation commit."
                ),
            },
        ],
        "packet_sha256": EXPECTED_SHA256[PACKET_REL],
        "contract_bundle_sha256": EXPECTED_SHA256[CONTRACT_REL],
        "residual_obligations": [
            "IMPLEMENT_ONLY_THE_FOUR_AUTHORIZED_READ_ONLY_PROTOTYPE_PATHS",
            "RUN_IMMUTABLE_PREFLIGHT_BEFORE_CREATING_ANY_PROTOTYPE_OUTPUT",
            "EXECUTE_EXACTLY_58_INHERITED_PLUS_18_RUNTIME_STAGE_A_CONTROLS",
            "DIRECTLY_INVOKE_THE_PRODUCTION_CONTROL_TEST_FROM_THE_STAGE_A_ORCHESTRATOR_AND_RECORD_IT_IN_EXECUTION_EVIDENCE",
            "DEFER_GOVERNANCE_MANIFEST_GITATTRIBUTES_DOCUMENTATION_AND_LEAN_INTEGRATION_UNTIL_POST_EXECUTION_REVIEW_OR_SUCCESSOR",
            "DO_NOT_BROADEN_THE_FOUR_PATH_CLEAN_IMPLEMENTATION_COMMIT",
            "PROVE_BYTE_EXACT_CUSTODY_AND_RUNTIME_SHADOW_PARITY",
            "COMMIT_STAGE_A_CANDIDATE_EVIDENCE_PENDING_INDEPENDENT_REVIEW",
            "PREPARE_A_VERSIONED_SUCCESSOR_BEFORE_ANY_STAGE_B_EXECUTION",
        ],
        "review_id": (
            "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_PACKET_"
            "INDEPENDENT_REVIEW_20260711_v0"
        ),
        "reviewed_commit": SOURCE_COMMIT,
        "schema_id": (
            "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_PACKET_"
            "INDEPENDENT_REVIEW_20260711_v0"
        ),
        "status": (
            "ACCEPTED_PREPARATION_PACKET_AND_AUTHORIZED_BOUNDED_STAGE_A_"
            "READ_ONLY_PROTOTYPE_EXECUTION_ONLY"
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
        description="Build or verify the read-only registry prototype packet review."
    )
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    raw = canonical_json_bytes(build_review())
    if args.check:
        if not OUTPUT_PATH.exists() or OUTPUT_PATH.read_bytes() != raw:
            raise IndependentReviewError("read-only prototype packet review drift")
        print(f"read_only_prototype_packet_review: OK sha256={_sha256(raw)}")
        return 0
    _atomic_write(OUTPUT_PATH, raw)
    print(f"read_only_prototype_packet_review: wrote sha256={_sha256(raw)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
