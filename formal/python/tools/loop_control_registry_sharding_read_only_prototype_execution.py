"""Fail-closed Stage-A loop-control registry prototype orchestrator.

The reviewed Stage-A v0 contract authorizes a read-only prototype attempt, but
its artifact graph is not constructively serializable.  The artifact-source
manifest must inventory the runtime run manifest, while that runtime manifest
must contain the actual SHA-256 and size of the artifact-source manifest.  The
cross-document contract then requires both identity objects to match the
inventoried bytes.  This creates a two-node cryptographic fixed-point problem:

    source manifest -> SHA(runtime manifest)
    runtime manifest -> SHA(source manifest)

No staging, placeholder, terminal-envelope, or inventory exclusion rule is
authorized by the reviewed contract.  Weakening either edge would silently
change the accepted contract.  This orchestrator therefore detects the cycle
before creating a run root and emits bounded machine-readable blocked evidence
to stdout.  It never writes the legacy registry or any prototype artifact.

A versioned successor can make execution possible by introducing a one-way
terminal envelope or by explicitly excluding the runtime manifest from the
source-manifest inventory.  Until then, claiming a 76-control Stage-A result
would be false.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
from typing import Any, Final, Sequence


REPO_ROOT: Final = Path(__file__).resolve().parents[3]
CONTRACT_REL: Final = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_"
    "CONTRACT_BUNDLE_20260711_v0.json"
)
CONTRACT_SHA256: Final = (
    "272279d414591b25b3a519d22d92659f4a662ce1c9cbd5fadf3067f1eaa8f0bb"
)
REVIEW_REL: Final = (
    "formal/docs/release/"
    "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_"
    "PACKET_INDEPENDENT_REVIEW_20260711_v0.json"
)
REVIEW_SHA256: Final = (
    "272e4eb60a1467c681f05ce7c161d3146cc0b2ff2b3ad6e08c98989e6a929f19"
)
AUTHORIZATION_REVIEW_COMMIT: Final = "d2d211c33885135d213bd9a9267901aad7ca7454"
SOURCE_MANIFEST_REL: Final = (
    "manifests/LOOP_CONTROL_ARTIFACT_SOURCE_MANIFEST_v1.json"
)
RUNTIME_MANIFEST_REL: Final = (
    "manifests/LOOP_CONTROL_READ_ONLY_PROTOTYPE_RUN_MANIFEST_v1.json"
)
PROTOTYPE_BASE_REL: Final = "formal/scratch/loop_control_registry_v1_prototype"
DIRECT_TEST_NODE: Final = (
    "formal/python/tests/test_loop_control_registry_v1_production_controls.py::"
    "test_direct_stage_a_control_harness"
)
BLOCK_CODE: Final = "STAGE_A-BLOCKED-ARTIFACT-HASH-CYCLE"


class StageABlockedError(RuntimeError):
    """A reviewed contract invariant prevents bounded Stage-A execution."""

    def __init__(self, code: str, message: str) -> None:
        super().__init__(message)
        self.code = code


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _load_reviewed_json(relative: str, expected_sha256: str) -> dict[str, Any]:
    path = REPO_ROOT / relative
    raw = path.read_bytes()
    observed = _sha256(raw)
    if observed != expected_sha256:
        raise StageABlockedError(
            "STAGE_A-BLOCKED-REVIEWED-BINDING-MISMATCH",
            f"{relative} SHA-256 {observed} != reviewed {expected_sha256}",
        )
    value = json.loads(raw.decode("utf-8"))
    if not isinstance(value, dict):
        raise StageABlockedError(
            "STAGE_A-BLOCKED-REVIEWED-BINDING-MISMATCH",
            f"{relative} is not a JSON object",
        )
    return value


def _git(*args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        cwd=REPO_ROOT,
        check=check,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )


def artifact_hash_dependency_graph(contract: dict[str, Any]) -> dict[str, list[str]]:
    """Derive the relevant hash-dependency edges from reviewed v0 facts."""

    artifact_contract = contract["artifact_source_and_candidate_tree_contract"]
    fixed = artifact_contract["fixed_path_to_artifact_kind"]
    runtime_schema = contract["runtime_schemas"]["runtime_run_manifest"]
    runtime_properties = runtime_schema["properties"]

    if fixed.get(RUNTIME_MANIFEST_REL) != "RUNTIME_RUN_MANIFEST":
        raise StageABlockedError(
            "STAGE_A-BLOCKED-CONTRACT-SHAPE",
            "runtime manifest is not mapped to its reviewed artifact kind",
        )
    if not artifact_contract.get(
        "all_other_regular_run_root_artifacts_are_inventoried_exactly_once"
    ):
        raise StageABlockedError(
            "STAGE_A-BLOCKED-CONTRACT-SHAPE",
            "reviewed complete-inventory invariant is absent",
        )
    if not artifact_contract.get("artifact_source_manifest_is_not_self_inventoried"):
        raise StageABlockedError(
            "STAGE_A-BLOCKED-CONTRACT-SHAPE",
            "reviewed source-manifest self-exclusion is absent",
        )
    source_identity = runtime_properties.get("artifact_source_manifest", {})
    required = set(source_identity.get("required", []))
    if required != {"path", "sha256", "size_bytes"}:
        raise StageABlockedError(
            "STAGE_A-BLOCKED-CONTRACT-SHAPE",
            "runtime manifest does not carry the reviewed source-manifest identity",
        )
    cross = set(artifact_contract.get("cross_document_invariants", []))
    required_cross = {
        "PATH_SHA256_SIZE_MATCH_ACTUAL_BYTES",
        "IDENTITY_OBJECTS_MATCH_INVENTORY_ROWS",
    }
    if not required_cross.issubset(cross):
        raise StageABlockedError(
            "STAGE_A-BLOCKED-CONTRACT-SHAPE",
            "reviewed actual-byte identity invariants are absent",
        )
    return {
        SOURCE_MANIFEST_REL: [RUNTIME_MANIFEST_REL],
        RUNTIME_MANIFEST_REL: [SOURCE_MANIFEST_REL],
    }


def _strongly_connected_pair(graph: dict[str, list[str]]) -> tuple[str, str] | None:
    for left, successors in graph.items():
        for right in successors:
            if left != right and left in graph.get(right, []):
                return tuple(sorted((left, right)))  # type: ignore[return-value]
    return None


def contract_preflight() -> dict[str, Any]:
    """Verify reviewed bytes and return the fail-closed contract diagnosis."""

    contract = _load_reviewed_json(CONTRACT_REL, CONTRACT_SHA256)
    review = _load_reviewed_json(REVIEW_REL, REVIEW_SHA256)
    if review.get("decision") != (
        "ACCEPT_PREPARATION_AND_AUTHORIZE_ONLY_BOUNDED_STAGE_A_76_CONTROL_"
        "READ_ONLY_PROTOTYPE_IMPLEMENTATION_AND_EXECUTION"
    ):
        raise StageABlockedError(
            "STAGE_A-BLOCKED-AUTHORIZATION",
            "independent review does not carry the reviewed bounded decision",
        )
    if review.get("implementation_integration_condition_review", {}).get(
        "production_control_test_must_be_invoked_directly_by_execution_orchestrator"
    ) is not True:
        raise StageABlockedError(
            "STAGE_A-BLOCKED-AUTHORIZATION",
            "direct production-control invocation requirement is absent",
        )
    graph = artifact_hash_dependency_graph(contract)
    pair = _strongly_connected_pair(graph)
    return {
        "schema_id": "LOOP_CONTROL_STAGE_A_BLOCKED_PREFLIGHT_v0",
        "status": "BLOCKED_BEFORE_RUN_ROOT_CREATION",
        "block_code": BLOCK_CODE if pair else None,
        "authorization_review_commit": AUTHORIZATION_REVIEW_COMMIT,
        "contract_path": CONTRACT_REL,
        "contract_sha256": CONTRACT_SHA256,
        "independent_review_path": REVIEW_REL,
        "independent_review_sha256": REVIEW_SHA256,
        "dependency_graph": graph,
        "strongly_connected_pair": list(pair) if pair else [],
        "run_root_created": False,
        "prototype_artifacts_created": False,
        "source_registry_modified": False,
        "controls_expected": 76,
        "controls_observed": 0,
        "stage_b_behavior": False,
        "message": (
            "The source manifest must hash the runtime manifest, while the runtime "
            "manifest must hash the source manifest. No reviewed one-way terminal "
            "binding or inventory exclusion exists."
            if pair
            else "No reviewed artifact hash cycle was found."
        ),
    }


def invoke_direct_production_control_test() -> dict[str, Any]:
    """Directly invoke the required node without creating a prototype run root."""

    command = [
        sys.executable,
        "-m",
        "pytest",
        "-q",
        "-p",
        "no:cacheprovider",
        DIRECT_TEST_NODE,
    ]
    environment = os.environ.copy()
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    environment.pop("TOE_REGISTRY_STAGE_A_RUN_ROOT", None)
    completed = subprocess.run(
        command,
        cwd=REPO_ROOT,
        env=environment,
        check=False,
        capture_output=True,
        text=False,
    )
    return {
        "exact_command": subprocess.list2cmdline(command),
        "test_path_and_id": DIRECT_TEST_NODE,
        "exit_code": completed.returncode,
        "stdout_sha256": _sha256(completed.stdout),
        "stderr_sha256": _sha256(completed.stderr),
        "stdout_size_bytes": len(completed.stdout),
        "stderr_size_bytes": len(completed.stderr),
        "stage_a_run_root_supplied": False,
        "direct_invocation_completed": True,
        "controls_observed": 0,
    }


def execute_stage_a() -> dict[str, Any]:
    """Run immutable preflight and stop safely on the reviewed SHA cycle."""

    result = contract_preflight()
    if result["block_code"]:
        result["production_control_test_invocation"] = (
            invoke_direct_production_control_test()
        )
        return result
    raise StageABlockedError(
        "STAGE_A-BLOCKED-IMPLEMENTATION-INCOMPLETE",
        "contract became executable but this blocked-v0 orchestrator was not superseded",
    )


def _parse_args(argv: Sequence[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check-contract",
        action="store_true",
        help="inspect reviewed contract dependencies without creating artifacts",
    )
    parser.add_argument(
        "--execute",
        action="store_true",
        help="attempt Stage A and emit a fail-closed blocked result to stdout",
    )
    args = parser.parse_args(argv)
    if args.check_contract == args.execute:
        parser.error("select exactly one of --check-contract or --execute")
    return args


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(argv)
    try:
        result = execute_stage_a() if args.execute else contract_preflight()
    except (OSError, KeyError, ValueError, StageABlockedError) as exc:
        payload = {
            "schema_id": "LOOP_CONTROL_STAGE_A_BLOCKED_PREFLIGHT_v0",
            "status": "BLOCKED_BEFORE_RUN_ROOT_CREATION",
            "block_code": getattr(exc, "code", "STAGE_A-BLOCKED-PREFLIGHT-ERROR"),
            "message": str(exc),
            "run_root_created": False,
            "prototype_artifacts_created": False,
            "source_registry_modified": False,
            "controls_expected": 76,
            "controls_observed": 0,
        }
        print(json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False))
        return 2
    print(json.dumps(result, indent=2, sort_keys=True, ensure_ascii=False))
    return 2 if result.get("block_code") else 0


if __name__ == "__main__":
    raise SystemExit(main())
