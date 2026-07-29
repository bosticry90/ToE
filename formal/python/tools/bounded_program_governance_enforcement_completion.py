"""Materialize immutable bounded-program manifests and legacy ID attestations.

This maintenance producer does not mutate the registry or any historical
OPEN/CLOSE, calculation, or review artifact.  It binds the already-closed
programs to their canonical stages and exact historical commit envelopes.
"""

from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path
from typing import Any, Iterable

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.bounded_program_governance import (
    NATIVE_MANDATORY_EXIT,
    NATIVE_PROGRAM_ID,
    NATIVE_STAGE_DEFINITIONS,
    QUADRATIC_MANDATORY_EXIT,
    QUADRATIC_PROGRAM_ID,
    QUADRATIC_STAGE_DEFINITIONS,
    REGISTRY_PATH,
    _event_hash,
    _pretty_json_bytes,
    _stage_scope,
    jcs_bytes,
    scope_hash,
    sha256_bytes,
    strict_json_load,
)


REPO_ROOT = find_repo_root(Path(__file__))
MANIFEST_ROOT = (
    REPO_ROOT / "formal" / "docs" / "release" / "bounded_program_manifests"
)
ATTESTATION_ROOT = (
    REPO_ROOT / "formal" / "docs" / "release" / "bounded_program_attestations"
)
BASELINE_COMMIT = "a1b6ccbbdae8456aad4af7d355ecfc781fc227ce"

PROGRAM_MANIFEST_PATHS = {
    QUADRATIC_PROGRAM_ID: (
        "formal/docs/release/bounded_program_manifests/"
        "QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0_MANIFEST_v1.json"
    ),
    NATIVE_PROGRAM_ID: (
        "formal/docs/release/bounded_program_manifests/"
        "TOE_NATIVE_SURROGATE_V0_MANIFEST_v1.json"
    ),
}
LEGACY_ATTESTATION_PATH = (
    "formal/docs/release/bounded_program_attestations/"
    "BOUNDED_PROGRAM_LEGACY_EVENT_COMMIT_ID_ATTESTATION_20260729_v0.json"
)

PROGRAM_CONTRACTS: dict[str, dict[str, Any]] = {
    QUADRATIC_PROGRAM_ID: {
        "stage_definitions": QUADRATIC_STAGE_DEFINITIONS,
        "mandatory_exit_target": QUADRATIC_MANDATORY_EXIT,
        "mandatory_exit_result_path": (
            "formal/output/"
            "CALC-QFT-GR-QUADRATIC-TOE-ROLE-AFTER-GENERIC-FROZEN-RESULT-v0.json"
        ),
        "mandatory_exit_review_path": (
            "formal/docs/release/"
            "QFT_GR_QUADRATIC_TOE_ROLE_AFTER_GENERIC_FROZEN_RESULT_REVIEW_20260729_v0.json"
        ),
        "expected_terminal_projection": {
            "mandatory_exit_completed": True,
            "program_terminal_status": "CLOSED_AFTER_MANDATORY_ROLE_GATE",
            "toe_role": "REFERENCE_CONTROL_ONLY",
            "control_result": "UNRESOLVED_AFTER_BOUNDED_ATTEMPT",
        },
        "mandatory_exit_result_assertions": {
            "terminal_outcome": (
                "REFERENCE_CONTROL_ONLY_WITH_UNRESOLVED_AFTER_BOUNDED_ATTEMPT"
            )
        },
        "mandatory_exit_review_assertions": {
            "quadratic_program_terminal": True,
            "toe_role": "REFERENCE_CONTROL_ONLY",
            "control_result": "UNRESOLVED_AFTER_BOUNDED_ATTEMPT",
        },
        "authorized_non_scientific_lifecycle_commits": [
            {
                "commit": "a479cde099aa722e32ef899d14f79e15ab7aaf87",
                "classification": "EXHAUSTIVE_LEAN_AGGREGATE_VALIDATION_REFRESH_ONLY",
                "scientific_target_created": False,
            }
        ],
    },
    NATIVE_PROGRAM_ID: {
        "stage_definitions": NATIVE_STAGE_DEFINITIONS,
        "mandatory_exit_target": NATIVE_MANDATORY_EXIT,
        "mandatory_exit_result_path": (
            "formal/output/CALC-TOE-NATIVE-SURROGATE-V0-BOUNDED-CLOSEOUT-v0.json"
        ),
        "mandatory_exit_review_path": (
            "formal/docs/release/"
            "TOE_NATIVE_SURROGATE_V0_BOUNDED_CLOSEOUT_REVIEW_20260729_v0.json"
        ),
        "expected_terminal_projection": {
            "mandatory_exit_selected": True,
            "mandatory_exit_completed": True,
            "program_terminal_status": "CLOSED_AFTER_MANDATORY_EXIT",
            "representation_outcome": "BLOCKED_CCFT_TO_CONTINUUM_MAP_UNRESOLVED",
            "phi_symmetry_status": "BLOCKED_TEST_MATTER_SYMMETRY_UNJUSTIFIED",
            "chi_symmetry_status": "BLOCKED_COHERENCE_Z2_UNJUSTIFIED",
            "stage_2_authorized": False,
            "v0_discriminator_result": "NO_UNIQUE_TOE_DISCRIMINATOR_V0",
        },
        "mandatory_exit_result_assertions": {
            "terminal_outcome": "NO_UNIQUE_TOE_DISCRIMINATOR_V0"
        },
        "mandatory_exit_review_assertions": {
            "program_terminal": True,
            "terminal_outcome": "NO_UNIQUE_TOE_DISCRIMINATOR_V0",
        },
        "authorized_non_scientific_lifecycle_commits": [],
    },
}


def _git(*args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def _introduction_commit(relative_path: str) -> str:
    commits = _git(
        "log",
        "--diff-filter=A",
        "--format=%H",
        "--",
        relative_path,
    ).splitlines()
    if len(commits) != 1:
        raise RuntimeError(
            f"expected exactly one introduction commit for {relative_path}, "
            f"found {len(commits)}"
        )
    return commits[0]


def _commit_paths(commit: str) -> list[str]:
    rows = _git(
        "diff-tree",
        "--no-commit-id",
        "--name-only",
        "-r",
        commit,
    ).splitlines()
    return sorted(row for row in rows if row)


def _hash_payload(payload: dict[str, Any], hash_field: str) -> str:
    return sha256_bytes(
        jcs_bytes({key: value for key, value in payload.items() if key != hash_field})
    )


def _event_by_type(
    registry_program: dict[str, Any], attempt: int, event_type: str
) -> tuple[str, dict[str, Any]]:
    refs = [
        row
        for row in registry_program["events"]
        if row["attempt_sequence_number"] == attempt
        and row["event_type"] == event_type
    ]
    if len(refs) != 1:
        raise RuntimeError(
            f"expected one {event_type} for attempt {attempt}, found {len(refs)}"
        )
    relative_path = refs[0]["path"]
    event = strict_json_load(REPO_ROOT / relative_path)
    if event["event_hash"] != _event_hash(event):
        raise RuntimeError(f"invalid historical event hash: {relative_path}")
    return relative_path, event


def build_program_manifest(program_id: str, registry: dict[str, Any]) -> dict[str, Any]:
    contract = PROGRAM_CONTRACTS[program_id]
    registry_program = registry["bounded_programs_v1"][program_id]
    attempted = set(registry_program["attempted_stage_ids"])
    stages: list[dict[str, Any]] = []
    for stage_number, definition in enumerate(
        contract["stage_definitions"], start=1
    ):
        semantic_stage_id = definition["semantic_stage_id"]
        row: dict[str, Any] = {
            "stage_number": stage_number,
            "semantic_stage_id": semantic_stage_id,
            "canonical_target": definition["target"],
            "canonical_scope": _stage_scope(definition),
            "canonical_scope_hash": scope_hash(_stage_scope(definition)),
            "mandatory_terminal_outcomes": definition[
                "terminal_outcome_vocabulary"
            ],
            "attempted": semantic_stage_id in attempted,
        }
        if row["attempted"]:
            open_path, _ = _event_by_type(
                registry_program, stage_number, "ATTEMPT_OPEN"
            )
            close_path, close_event = _event_by_type(
                registry_program, stage_number, "ATTEMPT_CLOSE"
            )
            open_commit = _introduction_commit(open_path)
            close_commit = _introduction_commit(close_path)
            row["historical_envelope"] = {
                "open_event_path": open_path,
                "open_introduction_commit": open_commit,
                "open_commit_exact_path_set": _commit_paths(open_commit),
                "close_event_path": close_path,
                "close_introduction_commit": close_commit,
                "close_commit_exact_path_set": _commit_paths(close_commit),
                "result_artifact_path": close_event["result_artifact_path"],
                "review_artifact_path": close_event["review_artifact_path"],
            }
        stages.append(row)

    exit_review_path = contract["mandatory_exit_review_path"]
    exit_commit = _introduction_commit(exit_review_path)
    non_scientific_commits = []
    for row in contract["authorized_non_scientific_lifecycle_commits"]:
        non_scientific_commits.append(
            {
                **row,
                "commit_exact_path_set": _commit_paths(row["commit"]),
            }
        )
    manifest: dict[str, Any] = {
        "schema_id": "toe.bounded_program.immutable_manifest.v1",
        "program_id": program_id,
        "created_from_closed_baseline_commit": BASELINE_COMMIT,
        "authorized_stage_count": len(stages),
        "repair_attempt_count": 0,
        "no_subsidiary_scientific_targets": True,
        "mandatory_exit": {
            "target": contract["mandatory_exit_target"],
            "result_artifact_path": contract["mandatory_exit_result_path"],
            "review_artifact_path": exit_review_path,
            "introduction_commit": exit_commit,
            "commit_exact_path_set": _commit_paths(exit_commit),
            "expected_terminal_projection": contract["expected_terminal_projection"],
            "result_assertions": contract["mandatory_exit_result_assertions"],
            "review_assertions": contract["mandatory_exit_review_assertions"],
        },
        "authorized_non_scientific_lifecycle_commits": non_scientific_commits,
        "stages": stages,
        "status": "IMMUTABLE_AUTHORITATIVE_PROGRAM_MANIFEST",
    }
    manifest["manifest_hash"] = _hash_payload(manifest, "manifest_hash")
    return manifest


def build_legacy_attestation(registry: dict[str, Any]) -> dict[str, Any]:
    entries: list[dict[str, Any]] = []
    native = registry["bounded_programs_v1"][NATIVE_PROGRAM_ID]
    for event_type, field in (
        ("ATTEMPT_OPEN", "opened_from_commit"),
        ("ATTEMPT_CLOSE", "closed_from_commit"),
    ):
        event_path, event = _event_by_type(native, 1, event_type)
        abbreviated = event[field]
        resolved = _git("rev-parse", f"{abbreviated}^{{commit}}")
        candidates = sorted(
            commit
            for commit in _git("rev-list", "--all").splitlines()
            if commit.startswith(abbreviated)
        )
        if candidates != [resolved]:
            raise RuntimeError(
                f"legacy commit ID is not unique: {abbreviated} -> {candidates}"
            )
        entries.append(
            {
                "legacy_event_path": event_path,
                "field": field,
                "stored_abbreviated_id": abbreviated,
                "resolved_full_commit_id": resolved,
                "uniqueness_candidate_count": 1,
                "uniqueness_candidates": candidates,
                "git_object_type": _git("cat-file", "-t", resolved),
            }
        )
    attestation: dict[str, Any] = {
        "schema_id": "toe.bounded_program.legacy_event_commit_id_attestation.v0",
        "captured_from_commit": BASELINE_COMMIT,
        "future_event_commit_id_policy": (
            "lowercase full 40-character commit IDs required"
        ),
        "entries": entries,
        "status": "IMMUTABLE_LEGACY_IDENTIFIER_CUSTODY_ATTESTATION",
    }
    attestation["attestation_hash"] = _hash_payload(
        attestation, "attestation_hash"
    )
    return attestation


def write_artifacts() -> None:
    registry = strict_json_load(REGISTRY_PATH)
    for program_id, relative_path in PROGRAM_MANIFEST_PATHS.items():
        path = REPO_ROOT / relative_path
        if path.exists():
            raise RuntimeError(f"immutable manifest already exists: {relative_path}")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(_pretty_json_bytes(build_program_manifest(program_id, registry)))
    attestation_path = REPO_ROOT / LEGACY_ATTESTATION_PATH
    if attestation_path.exists():
        raise RuntimeError(
            f"legacy attestation already exists: {LEGACY_ATTESTATION_PATH}"
        )
    attestation_path.parent.mkdir(parents=True, exist_ok=True)
    attestation_path.write_bytes(_pretty_json_bytes(build_legacy_attestation(registry)))


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("write",))
    args = parser.parse_args(list(argv) if argv is not None else None)
    if args.command == "write":
        write_artifacts()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
