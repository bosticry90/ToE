from __future__ import annotations

import hashlib
import json
import os
import subprocess
from pathlib import Path

import pytest

from formal.python.tools.bounded_program_governance import PROGRAMS_KEY
from formal.python.tools.native_hypothesis_census_index_v1 import (
    CENSUS_PROGRAM_ID,
    HashCache,
    ParserSpec,
    UnsafePathError,
    build_maintenance_trial,
    build_snapshot,
    compare_snapshots,
    git_blob_sha256,
    normalize_relative_path,
    passive_extract,
    schema_contract,
    shard_records,
)
from formal.python.tools.native_hypothesis_census_index_v1_profile import (
    build_profile,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
)
SCHEMA_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_HYPOTHESIS_CENSUS_INDEX_SCHEMA_V1.json"
)
RESULT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_CENSUS_INDEXING_AND_PERFORMANCE_MAINTENANCE_RESULT_20260730_v0.json"
)
DEPENDENCY_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_CENSUS_STAGE_1_DEPENDENCY_IMPACT_CHECK_20260730_v0.json"
)


def _write(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)


def _snapshot(
    root: Path,
    cache_path: Path,
    *,
    final: bool,
    extract_text: bool = True,
) -> dict:
    with HashCache(cache_path) as cache:
        return build_snapshot(
            source_root_id="SYNTHETIC_TEST_ROOT",
            root=root,
            cache=cache,
            final_hash_verification=final,
            extract_text=extract_text,
        )


def test_schema_contract_is_versioned_and_passive() -> None:
    contract = schema_contract()
    assert json.loads(SCHEMA_PATH.read_text(encoding="utf-8")) == contract
    assert contract["index_id"] == "TOE_NATIVE_HYPOTHESIS_CENSUS_INDEX_V1"
    assert contract["schema_version"] == 1
    assert contract["cache_never_replaces_final_hash_verification"] is True
    assert contract["tracked_primary_identity"] == "COMMITTED_GIT_BLOB_BYTES"
    assert contract["network_policy"] == "DENY"
    assert contract["recursive_archive_expansion"] == "DENY"
    assert contract["archived_active_content_execution"] == "DENY"
    assert len(contract["parser_specs"]) == 9


def test_path_normalization_rejects_escape_and_absolute_paths() -> None:
    assert normalize_relative_path("a/b.txt") == "a/b.txt"
    for value in ("../x", "a/../x", "/absolute", "C:/absolute", "a\x00b"):
        with pytest.raises(UnsafePathError):
            normalize_relative_path(value)


def test_snapshot_is_deterministic_and_exact_duplicates_remain_distinct(
    tmp_path: Path,
) -> None:
    root = tmp_path / "synthetic"
    _write(root / "a.md", b"# A\n")
    _write(root / "nested" / "b.md", b"# A\n")
    _write(root / "c.json", b'{"x": 1}\n')
    cache = tmp_path / "cache.sqlite3"

    first = _snapshot(root, cache, final=True)
    second = _snapshot(root, cache, final=True)

    assert first["snapshot_tuple_hash"] == second["snapshot_tuple_hash"]
    assert [row["custody_relative_path"] for row in first["records"]] == [
        "a.md",
        "c.json",
        "nested/b.md",
    ]
    duplicate_rows = [
        row
        for row in first["records"]
        if row["duplicate_group_candidate"] is not None
    ]
    assert len(duplicate_rows) == 2
    assert all(
        row["duplicate_group_candidate"].startswith(
            "EXACT_CONTENT_DUPLICATE:"
        )
        for row in duplicate_rows
    )


def test_cache_reuse_is_a_hint_and_final_scan_rehashes(tmp_path: Path) -> None:
    root = tmp_path / "synthetic"
    _write(root / "a.txt", b"one\n")
    cache = tmp_path / "cache.sqlite3"

    initial = _snapshot(root, cache, final=True)
    reused = _snapshot(root, cache, final=False)
    verified = _snapshot(root, cache, final=True)

    assert initial["performance"]["files_hashed"] == 1
    assert reused["performance"]["files_reused_from_cache"] == 1
    assert reused["performance"]["files_hashed"] == 0
    assert verified["performance"]["files_hashed"] == 1
    assert verified["performance"]["files_reused_from_cache"] == 0


def test_cache_invalidates_when_metadata_hint_changes(tmp_path: Path) -> None:
    root = tmp_path / "synthetic"
    path = root / "a.txt"
    _write(path, b"one\n")
    cache = tmp_path / "cache.sqlite3"
    _snapshot(root, cache, final=True)
    prior = path.stat().st_mtime_ns
    _write(path, b"two\n")
    os.utime(path, ns=(prior + 1_000_000, prior + 1_000_000))

    changed = _snapshot(root, cache, final=False)
    assert changed["performance"]["files_hashed"] == 1
    assert changed["performance"]["files_reused_from_cache"] == 0


def test_two_pass_snapshot_detects_added_removed_and_changed_files(
    tmp_path: Path,
) -> None:
    root = tmp_path / "synthetic"
    _write(root / "keep.txt", b"before\n")
    _write(root / "remove.txt", b"remove\n")
    cache = tmp_path / "cache.sqlite3"
    initial = _snapshot(root, cache, final=True)

    _write(root / "keep.txt", b"after\n")
    (root / "remove.txt").unlink()
    _write(root / "add.txt", b"add\n")
    final = _snapshot(root, cache, final=True)
    comparison = compare_snapshots(initial, final)

    assert comparison["stability_status"] == "SOURCE_ROOT_MUTATED_DURING_CENSUS"
    assert comparison["files_added_during_execution"] == ["add.txt"]
    assert comparison["files_removed_during_execution"] == ["remove.txt"]
    assert comparison["files_changed_during_execution"] == ["keep.txt"]


def test_archived_python_is_read_passively_and_never_executed(
    tmp_path: Path,
) -> None:
    root = tmp_path / "synthetic"
    marker = tmp_path / "should_not_exist.txt"
    code = (
        "from pathlib import Path\n"
        f"Path({str(marker)!r}).write_text('executed')\n"
    )
    _write(root / "payload.py", code.encode("utf-8"))
    snapshot = _snapshot(root, tmp_path / "cache.sqlite3", final=True)

    assert not marker.exists()
    assert snapshot["records"][0]["content_extraction_status"] == (
        "PASSIVE_TEXT_EXTRACTED"
    )


def test_container_and_binary_formats_are_metadata_only(tmp_path: Path) -> None:
    root = tmp_path / "synthetic"
    _write(root / "payload.zip", b"not-a-real-zip")
    _write(root / "payload.exe", b"MZ\x00\x00")
    snapshot = _snapshot(root, tmp_path / "cache.sqlite3", final=True)

    assert {
        row["content_extraction_status"] for row in snapshot["records"]
    } == {"METADATA_ONLY_NO_ACTIVE_CONTENT"}
    assert all(
        row["content_fingerprint"] is None for row in snapshot["records"]
    )


def test_passive_parser_enforces_size_text_and_nesting_limits(
    tmp_path: Path,
) -> None:
    path = tmp_path / "bounded.json"
    _write(path, b'{"a": {"b": {"c": 1}}}')
    size_spec = ParserSpec("TEST", ("json",), 4, 100, 5, 1024)
    text_spec = ParserSpec("TEST", ("json",), 100, 4, 5, 1024)
    nesting_spec = ParserSpec(
        "TEST",
        ("json",),
        100,
        100,
        5,
        1024,
        maximum_nesting_or_recursion_depth=2,
    )

    assert passive_extract(path, size_spec)["content_extraction_status"] == (
        "FILE_SIZE_LIMIT_EXCEEDED"
    )
    assert passive_extract(path, text_spec)["content_extraction_status"] == (
        "EXTRACTED_TEXT_LIMIT_REACHED"
    )
    assert passive_extract(path, nesting_spec)["content_extraction_status"] == (
        "NESTING_LIMIT_EXCEEDED"
    )


def test_symlink_escape_is_recorded_and_not_followed(tmp_path: Path) -> None:
    root = tmp_path / "synthetic"
    root.mkdir()
    outside = tmp_path / "outside.txt"
    outside.write_text("outside", encoding="utf-8")
    link = root / "escape.txt"
    try:
        link.symlink_to(outside)
    except OSError:
        pytest.skip("symlink creation is unavailable on this host")
    snapshot = _snapshot(root, tmp_path / "cache.sqlite3", final=True)
    row = snapshot["records"][0]
    assert row["filesystem_object_class"] == "LINK_OR_REPARSE_POINT"
    assert row["content_extraction_status"] == "SAFETY_BLOCKED_NO_FOLLOW"
    assert row["local_verified_sha256"] is None


def test_normalization_collision_is_preserved_and_blocked(
    tmp_path: Path,
) -> None:
    root = tmp_path / "synthetic"
    _write(root / "\u00e9.txt", b"one")
    try:
        _write(root / "e\u0301.txt", b"two")
    except OSError:
        pytest.skip("host filesystem normalizes Unicode filenames")
    snapshot = _snapshot(root, tmp_path / "cache.sqlite3", final=True)
    if len(snapshot["records"]) < 2:
        pytest.skip("host filesystem collapsed Unicode filenames")
    assert len(snapshot["filename_normalization_collisions"]) == 1
    assert all(
        row["content_extraction_status"]
        == "FILENAME_NORMALIZATION_COLLISION_BLOCKED"
        for row in snapshot["records"]
    )


def test_batch_sharding_is_deterministic_complete_and_nonoverlapping(
    tmp_path: Path,
) -> None:
    root = tmp_path / "synthetic"
    for index in range(17):
        _write(root / f"file-{index:02d}.txt", f"{index}\n".encode())
    snapshot = _snapshot(root, tmp_path / "cache.sqlite3", final=True)

    batches_a, aggregate_a = shard_records(snapshot["records"], 8)
    batches_b, aggregate_b = shard_records(snapshot["records"], 8)
    assert batches_a == batches_b
    assert aggregate_a == aggregate_b
    paths = [
        row["custody_relative_path"]
        for batch in batches_a
        for row in batch["records"]
    ]
    assert len(paths) == len(set(paths)) == 17
    assert aggregate_a["coverage_without_overlap_or_omission"] is True


def test_git_blob_identity_is_cached_by_object_id(tmp_path: Path) -> None:
    repo = tmp_path / "repo"
    repo.mkdir()
    subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
    _write(repo / "tracked.txt", b"committed bytes\n")
    subprocess.run(["git", "add", "tracked.txt"], cwd=repo, check=True)
    subprocess.run(
        [
            "git",
            "-c",
            "user.name=Test",
            "-c",
            "user.email=test@example.invalid",
            "commit",
            "-qm",
            "test",
        ],
        cwd=repo,
        check=True,
    )
    object_id = subprocess.run(
        ["git", "rev-parse", "HEAD:tracked.txt"],
        cwd=repo,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    with HashCache(tmp_path / "cache.sqlite3") as cache:
        first, first_cached = git_blob_sha256(repo, object_id, cache)
        second, second_cached = git_blob_sha256(repo, object_id, cache)
    assert first == hashlib.sha256(b"committed bytes\n").hexdigest()
    assert second == first
    assert first_cached is False
    assert second_cached is True


def test_maintenance_trial_refuses_scientific_archive_roots() -> None:
    with pytest.raises(UnsafePathError):
        build_maintenance_trial(
            REPO_ROOT / "archive",
            REPO_ROOT / ".toe_cache" / "must-not-be-created.sqlite3",
            "PROHIBITED_ARCHIVE_TRIAL",
        )


def test_program_remains_unopened_and_no_stage_one_index_exists() -> None:
    registry = json.loads(REGISTRY_PATH.read_text(encoding="utf-8"))
    program = registry[PROGRAMS_KEY][CENSUS_PROGRAM_ID]
    assert program["state"] == "UNOPENED"
    assert program["attempted_stage_ids"] == []
    assert program["events"] == []
    assert program["current_stage_number"] == 0
    assert program["program_terminal_status"] == "INSTALLED_UNOPENED"
    assert not (
        REPO_ROOT
        / "formal"
        / "output"
        / "native_hypothesis_census_v1"
        / "REPOSITORY_WIDE_SOURCE_CENSUS"
        / "aggregate_manifest.json"
    ).exists()


def test_profile_uses_only_generated_nonauthoritative_content() -> None:
    profile = build_profile(40)
    assert profile["status"] == "SYNTHETIC_NONAUTHORITATIVE_PROFILE_COMPLETE"
    assert profile["scientific_archive_traversed"] is False
    assert profile["authoritative_census_index_generated"] is False
    assert profile["synthetic_corpus"]["file_count"] == 40
    assert profile["snapshot_stability"] == "SOURCE_ROOT_SNAPSHOT_STABLE"
    assert profile["batch_coverage"] is True
    assert profile["warm_metadata_hint_cache_scan"][
        "files_reused_from_cache"
    ] == 40
    assert profile["final_verified_scan"]["files_hashed"] == 40


def test_maintenance_result_is_hash_bound_and_non_scientific() -> None:
    result = json.loads(RESULT_PATH.read_text(encoding="utf-8"))
    for output in result["outputs"]:
        path = REPO_ROOT / output["path"]
        assert hashlib.sha256(path.read_bytes()).hexdigest() == output["sha256"]
    assert result["preserved_program_state"] == "INSTALLED_UNOPENED"
    assert result["scientific_stage_1_authorized"] is False
    assert result["scientific_archive_traversed"] is False
    assert result["authoritative_census_index_generated"] is False
    assert all(result["checks"].values())


def test_dependency_impact_does_not_claim_exhaustive_python_passage() -> None:
    dependency = json.loads(DEPENDENCY_PATH.read_text(encoding="utf-8"))
    assert dependency["impact_conclusion"] == (
        "KNOWN_EXHAUSTIVE_FAILURES_DO_NOT_REACH_CENSUS_DEPENDENCIES"
    )
    assert dependency["stage_1_open_permitted_by_dependency_check"] is True
    assert dependency["scientific_stage_1_authorized"] is False
    assert dependency["exhaustive_python_debt"][
        "exhaustive_passage_established"
    ] is False
    assert dependency["scoped_validation"]["passed"] == 88
    assert dependency["scoped_validation"]["failed"] == 0
