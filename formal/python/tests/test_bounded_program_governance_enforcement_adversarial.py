from __future__ import annotations

import copy
import json
import shutil
import subprocess
from pathlib import Path
from typing import Callable

import pytest

from formal.python.tools.bounded_program_governance import (
    BoundedProgramError,
    LEGACY_ATTESTATION_PATH,
    PROGRAM_MANIFEST_PATHS,
    PROGRAMS_KEY,
    QUADRATIC_STAGE_DEFINITIONS,
    QUADRATIC_PROGRAM_ID,
    REGISTRY_PATH,
    _event_hash,
    _hashed_payload,
    _pretty_json_bytes,
    _stage_scope,
    jcs_bytes,
    scope_hash,
    sha256_bytes,
    sha256_path,
    strict_json_load,
    validate_event_chain,
)


REPO_ROOT = Path(__file__).resolve().parents[3]


def _registry() -> dict:
    return strict_json_load(REGISTRY_PATH)


def _copy_validation_tree(tmp_path: Path, registry: dict) -> None:
    paths = {LEGACY_ATTESTATION_PATH, *PROGRAM_MANIFEST_PATHS.values()}
    for program in registry[PROGRAMS_KEY].values():
        for reference in program["events"]:
            paths.add(reference["path"])
            event = strict_json_load(REPO_ROOT / reference["path"])
            if event["event_type"] == "ATTEMPT_CLOSE":
                paths.add(event["result_artifact_path"])
                paths.add(event["review_artifact_path"])
        manifest = strict_json_load(REPO_ROOT / program["program_manifest"]["path"])
        paths.add(manifest["mandatory_exit"]["result_artifact_path"])
        paths.add(manifest["mandatory_exit"]["review_artifact_path"])
    for relative_path in paths:
        destination = tmp_path / relative_path
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(REPO_ROOT / relative_path, destination)


def _rechain_program(
    registry: dict, tmp_path: Path, program_id: str
) -> list[dict]:
    previous_hash = None
    latest_open_hash = None
    events = []
    program = registry[PROGRAMS_KEY][program_id]
    for number, reference in enumerate(program["events"], start=1):
        path = tmp_path / reference["path"]
        event = json.loads(path.read_text(encoding="utf-8"))
        event["event_sequence_number"] = number
        event["previous_event_hash"] = previous_hash
        if event["event_type"] == "ATTEMPT_OPEN":
            latest_open_hash = None
        else:
            event["open_event_hash"] = latest_open_hash
        event["event_hash"] = _event_hash(event)
        path.write_bytes(_pretty_json_bytes(event))
        reference["event_type"] = event["event_type"]
        reference["attempt_sequence_number"] = event["attempt_sequence_number"]
        reference["event_hash"] = event["event_hash"]
        reference["sha256"] = sha256_bytes(path.read_bytes())
        previous_hash = event["event_hash"]
        if event["event_type"] == "ATTEMPT_OPEN":
            latest_open_hash = previous_hash
        events.append(event)
    program["event_chain_tip_hash"] = previous_hash
    return events


def _mutate_event(
    registry: dict,
    tmp_path: Path,
    *,
    program_id: str,
    event_index: int,
    mutation: Callable[[dict], None],
    rechain: bool = True,
) -> None:
    reference = registry[PROGRAMS_KEY][program_id]["events"][event_index]
    path = tmp_path / reference["path"]
    event = json.loads(path.read_text(encoding="utf-8"))
    mutation(event)
    event["event_hash"] = _event_hash(event)
    path.write_bytes(_pretty_json_bytes(event))
    reference["event_hash"] = event["event_hash"]
    reference["sha256"] = sha256_bytes(path.read_bytes())
    if rechain:
        _rechain_program(registry, tmp_path, program_id)


@pytest.mark.parametrize(
    ("mutation", "message"),
    [
        (
            lambda program: program.__setitem__(
                "attempted_stage_ids",
                ["CONSTRAINT_TANGENT_AND_PHYSICAL_QUOTIENT"],
            ),
            "attempted_stage_ids",
        ),
        (
            lambda program: program.__setitem__(
                "attempted_stage_ids", program["attempted_stage_ids"][:-1]
            ),
            "attempted_stage_ids",
        ),
        (
            lambda program: program.__setitem__(
                "blocked_stage_id", "COMPONENT_EXPANDED_LINEARIZATION"
            ),
            "blocked_stage_id",
        ),
        (
            lambda program: program.__setitem__(
                "no_subsidiary_scientific_targets", False
            ),
            "subsidiary scientific targets",
        ),
        (
            lambda program: program.__setitem__(
                "mandatory_exit_target", "renamed_exit"
            ),
            "mandatory exit target",
        ),
        (
            lambda program: program.__setitem__("mandatory_exit_completed", False),
            "mandatory_exit_completed",
        ),
        (
            lambda program: program.__setitem__("authorized_stage_count", 2),
            "authorization|authorized stage count",
        ),
        (
            lambda program: program.__setitem__("repair_attempt_count", 1),
            "repair_attempt_count",
        ),
    ],
)
def test_registry_projection_mutations_fail_closed(
    mutation: Callable[[dict], None], message: str
) -> None:
    registry = _registry()
    mutation(registry[PROGRAMS_KEY][QUADRATIC_PROGRAM_ID])
    with pytest.raises(BoundedProgramError, match=message):
        validate_event_chain(registry)


@pytest.mark.parametrize(
    ("field", "replacement", "message"),
    [
        (
            "semantic_stage_id",
            "RENAMED_BLOCKED_STAGE",
            "semantic stage differs",
        ),
        ("target", "renamed_scientific_target", "target differs"),
        ("scope_hash", "0" * 64, "scope hash differs"),
    ],
)
def test_open_manifest_binding_mutations_fail_closed(
    tmp_path: Path, field: str, replacement: str, message: str
) -> None:
    registry = _registry()
    _copy_validation_tree(tmp_path, registry)
    _mutate_event(
        registry,
        tmp_path,
        program_id=QUADRATIC_PROGRAM_ID,
        event_index=0,
        mutation=lambda event: event.__setitem__(field, replacement),
    )
    with pytest.raises(BoundedProgramError, match=message):
        validate_event_chain(registry, repo_root=tmp_path)


def test_blocked_stage_cannot_reappear_under_a_new_target(tmp_path: Path) -> None:
    registry = _registry()
    _copy_validation_tree(tmp_path, registry)
    program = registry[PROGRAMS_KEY][QUADRATIC_PROGRAM_ID]
    relative_path = "formal/docs/release/bounded_program_events/renamed_retry.json"
    event = {
        "event_type": "ATTEMPT_OPEN",
        "event_sequence_number": 7,
        "attempt_sequence_number": 4,
        "program_id": QUADRATIC_PROGRAM_ID,
        "semantic_stage_id": "EXACT_FROZEN_COMPANION_OPERATOR",
        "target": "renamed_companion_retry",
        "scope_hash": "0" * 64,
        "registry_snapshot_hash": "0" * 64,
        "previous_event_hash": program["event_chain_tip_hash"],
        "opened_from_commit": "a" * 40,
    }
    event["event_hash"] = _event_hash(event)
    path = tmp_path / relative_path
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(_pretty_json_bytes(event))
    program["events"].append(
        {
            "event_type": "ATTEMPT_OPEN",
            "attempt_sequence_number": 4,
            "path": relative_path,
            "event_hash": event["event_hash"],
            "sha256": sha256_bytes(path.read_bytes()),
        }
    )
    program["event_chain_tip_hash"] = event["event_hash"]
    with pytest.raises(BoundedProgramError, match="after blocked stage"):
        validate_event_chain(registry, repo_root=tmp_path)


def test_close_link_to_wrong_open_fails_closed(tmp_path: Path) -> None:
    registry = _registry()
    _copy_validation_tree(tmp_path, registry)
    _mutate_event(
        registry,
        tmp_path,
        program_id=QUADRATIC_PROGRAM_ID,
        event_index=1,
        mutation=lambda event: event.__setitem__("open_event_hash", "0" * 64),
        rechain=False,
    )
    with pytest.raises(BoundedProgramError, match="does not reference its OPEN"):
        validate_event_chain(registry, repo_root=tmp_path)


def test_removed_older_event_fails_closed() -> None:
    registry = _registry()
    program = registry[PROGRAMS_KEY][QUADRATIC_PROGRAM_ID]
    program["events"].pop(0)
    with pytest.raises(BoundedProgramError, match="event sequence"):
        validate_event_chain(registry)


def test_broken_previous_event_hash_fails_closed(tmp_path: Path) -> None:
    registry = _registry()
    _copy_validation_tree(tmp_path, registry)
    _mutate_event(
        registry,
        tmp_path,
        program_id=QUADRATIC_PROGRAM_ID,
        event_index=1,
        mutation=lambda event: event.__setitem__("previous_event_hash", "0" * 64),
        rechain=False,
    )
    with pytest.raises(BoundedProgramError, match="hash chain"):
        validate_event_chain(registry, repo_root=tmp_path)


def test_second_open_before_close_fails_closed(tmp_path: Path) -> None:
    registry = _registry()
    _copy_validation_tree(tmp_path, registry)
    program = registry[PROGRAMS_KEY][QUADRATIC_PROGRAM_ID]
    first = strict_json_load(tmp_path / program["events"][0]["path"])
    relative_path = "formal/docs/release/bounded_program_events/second_open.json"
    second = copy.deepcopy(first)
    second["event_sequence_number"] = 2
    second["attempt_sequence_number"] = 2
    second["semantic_stage_id"] = "COMPONENT_EXPANDED_LINEARIZATION"
    second["previous_event_hash"] = first["event_hash"]
    second["event_hash"] = _event_hash(second)
    path = tmp_path / relative_path
    path.write_bytes(_pretty_json_bytes(second))
    program["events"].insert(
        1,
        {
            "event_type": "ATTEMPT_OPEN",
            "attempt_sequence_number": 2,
            "path": relative_path,
            "event_hash": second["event_hash"],
            "sha256": sha256_bytes(path.read_bytes()),
        },
    )
    with pytest.raises(BoundedProgramError, match="second|prior CLOSE"):
        validate_event_chain(registry, repo_root=tmp_path)


def test_later_manifest_stage_cannot_open_after_block(tmp_path: Path) -> None:
    registry = _registry()
    _copy_validation_tree(tmp_path, registry)
    program = registry[PROGRAMS_KEY][QUADRATIC_PROGRAM_ID]
    manifest = strict_json_load(
        tmp_path / PROGRAM_MANIFEST_PATHS[QUADRATIC_PROGRAM_ID]
    )
    stage = manifest["stages"][3]
    relative_path = "formal/docs/release/bounded_program_events/stage4_after_block.json"
    event = {
        "event_type": "ATTEMPT_OPEN",
        "event_sequence_number": 7,
        "attempt_sequence_number": 4,
        "program_id": QUADRATIC_PROGRAM_ID,
        "semantic_stage_id": stage["semantic_stage_id"],
        "target": stage["canonical_target"],
        "scope_hash": stage["canonical_scope_hash"],
        "registry_snapshot_hash": "0" * 64,
        "previous_event_hash": program["event_chain_tip_hash"],
        "opened_from_commit": "a" * 40,
    }
    event["event_hash"] = _event_hash(event)
    path = tmp_path / relative_path
    path.write_bytes(_pretty_json_bytes(event))
    program["events"].append(
        {
            "event_type": "ATTEMPT_OPEN",
            "attempt_sequence_number": 4,
            "path": relative_path,
            "event_hash": event["event_hash"],
            "sha256": sha256_bytes(path.read_bytes()),
        }
    )
    program["event_chain_tip_hash"] = event["event_hash"]
    with pytest.raises(BoundedProgramError, match="after blocked stage"):
        validate_event_chain(registry, repo_root=tmp_path)


def test_rewritten_older_event_bytes_fail_closed(tmp_path: Path) -> None:
    registry = _registry()
    _copy_validation_tree(tmp_path, registry)
    event_path = (
        tmp_path
        / registry[PROGRAMS_KEY][QUADRATIC_PROGRAM_ID]["events"][0]["path"]
    )
    event = json.loads(event_path.read_text(encoding="utf-8"))
    event["unauthorized_rewrite_marker"] = True
    event_path.write_bytes(_pretty_json_bytes(event))
    with pytest.raises(BoundedProgramError, match="event byte hash mismatch"):
        validate_event_chain(registry, repo_root=tmp_path)


def _run_git(repo: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=repo,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def _write_payload(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(_pretty_json_bytes(payload))


def _synthetic_history(
    tmp_path: Path, mutation: str
) -> tuple[Path, dict, dict[str, str]]:
    repo = tmp_path / "repo"
    repo.mkdir()
    _run_git(repo, "init", "-q")
    _run_git(repo, "config", "user.name", "Governance Test")
    _run_git(repo, "config", "user.email", "governance@example.test")

    program_id = "SYNTHETIC_BOUNDED_PROGRAM_V0"
    manifest_path = "formal/docs/release/bounded_program_manifests/synthetic.json"
    attestation_path = (
        "formal/docs/release/bounded_program_attestations/synthetic.json"
    )
    registry_path = "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
    open_path = "formal/docs/release/bounded_program_events/open.json"
    close_path = "formal/docs/release/bounded_program_events/close.json"
    result_path = "formal/output/stage-result.json"
    review_path = "formal/docs/release/stage-review.json"
    exit_result_path = "formal/output/exit-result.json"
    exit_review_path = "formal/docs/release/exit-review.json"
    stage_definition = copy.deepcopy(QUADRATIC_STAGE_DEFINITIONS[0])
    stage_projection = copy.deepcopy(stage_definition)
    stage_projection["stage_number"] = 1
    stage_projection["scope_hash"] = scope_hash(_stage_scope(stage_definition))
    program = {
        "program_id": program_id,
        "authorized_stage_count": 1,
        "current_stage_number": 0,
        "attempted_stage_ids": [],
        "blocked_stage_id": None,
        "repair_attempt_count": 0,
        "mandatory_exit_target": "synthetic_mandatory_exit",
        "no_subsidiary_scientific_targets": True,
        "event_chain_tip_hash": None,
        "last_closed_attempt_number": 0,
        "state": "UNOPENED",
        "open_attempt_number": None,
        "events": [],
        "stage_definitions": [stage_projection],
    }
    registry = {
        "schema_id": "LOOP_CONTROL_REGISTRY_v0",
        "schema_version": 1,
        PROGRAMS_KEY: {program_id: program},
    }
    if mutation == "result_before_open":
        _write_payload(repo / result_path, {"stage": "result"})
    _write_payload(repo / registry_path, registry)
    _run_git(repo, "add", "--all")
    _run_git(repo, "commit", "-q", "-m", "base")
    base_commit = _run_git(repo, "rev-parse", "HEAD")
    base_registry_bytes = (repo / registry_path).read_bytes()

    opened_from = "f" * 40 if mutation == "wrong_open_parent" else base_commit
    snapshot_hash = (
        "0" * 64
        if mutation == "wrong_registry_snapshot"
        else sha256_bytes(base_registry_bytes)
    )
    open_event = {
        "event_type": "ATTEMPT_OPEN",
        "event_sequence_number": 1,
        "attempt_sequence_number": 1,
        "program_id": program_id,
        "semantic_stage_id": stage_definition["semantic_stage_id"],
        "target": stage_definition["target"],
        "scope_hash": stage_projection["scope_hash"],
        "registry_snapshot_hash": snapshot_hash,
        "previous_event_hash": None,
        "opened_from_commit": opened_from,
    }
    open_event["event_hash"] = _event_hash(open_event)
    _write_payload(repo / open_path, open_event)
    program.update(
        {
            "current_stage_number": 1,
            "attempted_stage_ids": [stage_definition["semantic_stage_id"]],
            "event_chain_tip_hash": open_event["event_hash"],
            "state": "OPEN",
            "open_attempt_number": 1,
        }
    )
    program["events"].append(
        {
            "event_type": "ATTEMPT_OPEN",
            "attempt_sequence_number": 1,
            "path": open_path,
            "event_hash": open_event["event_hash"],
            "sha256": sha256_path(repo / open_path),
        }
    )
    _write_payload(repo / registry_path, registry)
    _run_git(repo, "add", "--all")
    _run_git(repo, "commit", "-q", "-m", "open")
    open_commit = _run_git(repo, "rev-parse", "HEAD")

    if mutation == "artifacts_before_close":
        if not (repo / result_path).exists():
            _write_payload(repo / result_path, {"stage": "result"})
        _write_payload(repo / review_path, {"stage": "review"})
        _run_git(repo, "add", "--all")
        _run_git(repo, "commit", "-q", "-m", "premature stage artifacts")
    close_parent = _run_git(repo, "rev-parse", "HEAD")
    if not (repo / result_path).exists():
        _write_payload(repo / result_path, {"stage": "result"})
    if not (repo / review_path).exists():
        _write_payload(repo / review_path, {"stage": "review"})
    closed_from = "e" * 40 if mutation == "wrong_close_parent" else close_parent
    close_event = {
        "event_type": "ATTEMPT_CLOSE",
        "event_sequence_number": 2,
        "attempt_sequence_number": 1,
        "program_id": program_id,
        "open_event_hash": open_event["event_hash"],
        "result_artifact_path": result_path,
        "result_artifact_hash": sha256_path(repo / result_path),
        "review_artifact_path": review_path,
        "review_artifact_hash": sha256_path(repo / review_path),
        "terminal_result": "BLOCKED",
        "previous_event_hash": open_event["event_hash"],
        "closed_from_commit": closed_from,
    }
    close_event["event_hash"] = _event_hash(close_event)
    _write_payload(repo / close_path, close_event)
    if mutation == "output_outside_inventory":
        _write_payload(repo / "formal/output/unmanifested-stage-output.json", {"x": 1})
    program.update(
        {
            "blocked_stage_id": stage_definition["semantic_stage_id"],
            "event_chain_tip_hash": close_event["event_hash"],
            "last_closed_attempt_number": 1,
            "state": "CLOSED",
            "open_attempt_number": None,
        }
    )
    program["events"].append(
        {
            "event_type": "ATTEMPT_CLOSE",
            "attempt_sequence_number": 1,
            "path": close_path,
            "event_hash": close_event["event_hash"],
            "sha256": sha256_path(repo / close_path),
        }
    )
    _write_payload(repo / registry_path, registry)
    _run_git(repo, "add", "--all")
    _run_git(repo, "commit", "-q", "-m", "close")
    close_commit = _run_git(repo, "rev-parse", "HEAD")

    if mutation == "unmanifested_lifecycle_target":
        _write_payload(
            repo / "formal/output/unmanifested-scientific-target.json",
            {"target": "prepare_hidden_retry"},
        )
        _run_git(repo, "add", "--all")
        _run_git(repo, "commit", "-q", "-m", "hidden subsidiary target")

    _write_payload(
        repo / exit_result_path, {"terminal_outcome": "SYNTHETIC_EXIT"}
    )
    _write_payload(
        repo / exit_review_path,
        {"program_terminal": True, "terminal_outcome": "SYNTHETIC_EXIT"},
    )
    program.update(
        {
            "mandatory_exit_completed": True,
            "program_terminal_status": "CLOSED_AFTER_MANDATORY_EXIT",
        }
    )
    _write_payload(repo / registry_path, registry)
    _run_git(repo, "add", "--all")
    _run_git(repo, "commit", "-q", "-m", "mandatory exit")
    exit_commit = _run_git(repo, "rev-parse", "HEAD")

    def commit_paths(commit: str) -> list[str]:
        return sorted(
            row
            for row in _run_git(
                repo,
                "diff-tree",
                "--no-commit-id",
                "--name-only",
                "-r",
                commit,
            ).splitlines()
            if row
        )

    close_paths = commit_paths(close_commit)
    if mutation == "output_outside_inventory":
        close_paths.remove("formal/output/unmanifested-stage-output.json")
    manifest = {
        "schema_id": "toe.bounded_program.immutable_manifest.v1",
        "program_id": program_id,
        "created_from_closed_baseline_commit": exit_commit,
        "authorized_stage_count": 1,
        "repair_attempt_count": 0,
        "no_subsidiary_scientific_targets": True,
        "mandatory_exit": {
            "target": "synthetic_mandatory_exit",
            "result_artifact_path": exit_result_path,
            "review_artifact_path": exit_review_path,
            "introduction_commit": exit_commit,
            "commit_exact_path_set": commit_paths(exit_commit),
            "expected_terminal_projection": {
                "mandatory_exit_completed": True,
                "program_terminal_status": "CLOSED_AFTER_MANDATORY_EXIT",
            },
            "result_assertions": {"terminal_outcome": "SYNTHETIC_EXIT"},
            "review_assertions": {
                "program_terminal": True,
                "terminal_outcome": "SYNTHETIC_EXIT",
            },
        },
        "authorized_non_scientific_lifecycle_commits": [],
        "stages": [
            {
                "stage_number": 1,
                "semantic_stage_id": stage_definition["semantic_stage_id"],
                "canonical_target": stage_definition["target"],
                "canonical_scope": _stage_scope(stage_definition),
                "canonical_scope_hash": stage_projection["scope_hash"],
                "mandatory_terminal_outcomes": stage_definition[
                    "terminal_outcome_vocabulary"
                ],
                "attempted": True,
                "historical_envelope": {
                    "open_event_path": open_path,
                    "open_introduction_commit": open_commit,
                    "open_commit_exact_path_set": commit_paths(open_commit),
                    "close_event_path": close_path,
                    "close_introduction_commit": close_commit,
                    "close_commit_exact_path_set": close_paths,
                    "result_artifact_path": result_path,
                    "review_artifact_path": review_path,
                },
            }
        ],
        "status": "IMMUTABLE_AUTHORITATIVE_PROGRAM_MANIFEST",
    }
    manifest["manifest_hash"] = _hashed_payload(manifest, "manifest_hash")
    attestation = {
        "schema_id": "toe.bounded_program.legacy_event_commit_id_attestation.v0",
        "captured_from_commit": exit_commit,
        "future_event_commit_id_policy": (
            "lowercase full 40-character commit IDs required"
        ),
        "entries": [],
        "status": "IMMUTABLE_LEGACY_IDENTIFIER_CUSTODY_ATTESTATION",
    }
    attestation["attestation_hash"] = _hashed_payload(
        attestation, "attestation_hash"
    )
    _write_payload(repo / manifest_path, manifest)
    _write_payload(repo / attestation_path, attestation)
    program["program_manifest"] = {
        "path": manifest_path,
        "sha256": sha256_path(repo / manifest_path),
        "manifest_hash": manifest["manifest_hash"],
    }
    registry["schema_version"] = 2
    registry["bounded_program_governance_enforcement_v2"] = {"installed": True}
    _write_payload(repo / registry_path, registry)
    _run_git(repo, "add", "--all")
    _run_git(repo, "commit", "-q", "-m", "install enforcement")
    return repo, registry, {
        "program_id": program_id,
        "manifest_path": manifest_path,
        "attestation_path": attestation_path,
        "open_path": open_path,
    }


@pytest.mark.parametrize(
    ("mutation", "message"),
    [
        ("wrong_open_parent", "event parent is not a commit|OPEN parent mismatch"),
        ("wrong_close_parent", "event parent is not a commit|CLOSE parent mismatch"),
        ("wrong_registry_snapshot", "registry snapshot hash mismatch"),
        ("result_before_open", "not introduced atomically"),
        ("artifacts_before_close", "not introduced atomically"),
        ("unmanifested_lifecycle_target", "unmanifested subsidiary"),
        ("output_outside_inventory", "escaped its manifest envelope"),
    ],
)
def test_git_history_mutations_fail_for_the_intended_reason(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    mutation: str,
    message: str,
) -> None:
    import formal.python.tools.bounded_program_governance as governance

    repo, registry, paths = _synthetic_history(tmp_path, mutation)
    monkeypatch.setattr(
        governance,
        "PROGRAM_MANIFEST_PATHS",
        {paths["program_id"]: paths["manifest_path"]},
    )
    monkeypatch.setattr(
        governance,
        "LEGACY_ATTESTATION_PATH",
        paths["attestation_path"],
    )
    with pytest.raises(BoundedProgramError, match=message):
        validate_event_chain(registry, repo_root=repo, verify_git_history=True)
