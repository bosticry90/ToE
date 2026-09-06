from __future__ import annotations

import shutil
from pathlib import Path

import pytest

from formal.python.tools import qm_gr_criteria_hash_refresh as tool


STALE_BY_LABEL = {
    "QM_FULL_DERIVATION_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0": (
        "3925b71a53f85580e0fc22f48404cae71565b27926629b60aa3f702fe7b41ff1"
    ),
    "GR_CONTINUUM_LIMIT_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0": (
        "aefe5054b14554a3e3ec1607f27558002e2faab8a6e0b06bd13b90329ecf83e8"
    ),
    "GR_STRONG_FIELD_REGIME_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0": (
        "30c207b6f0e880f90a4295257cbe7af4a12a5c653bc86110359a9990c9bfcf00"
    ),
    "QM_GR_INTEGRATED_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0": (
        "51363f7dea1beef11cfd4f0f3f309fc2bdf241d870da0f0ffbfdd4864188afb4"
    ),
}


def _relevant_paths() -> tuple[str, ...]:
    return tuple(
        dict.fromkeys(
            item
            for spec in tool.DEFAULT_SPECS
            for item in (spec.artifact_relpath, *spec.token_files)
        )
    )


def _copy_relevant_tree(destination: Path) -> None:
    for rel in _relevant_paths():
        target = destination / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(tool.REPO_ROOT / rel, target)


def _make_all_tokens_stale(root: Path) -> None:
    for spec in tool.DEFAULT_SPECS:
        current = tool._sha256_file(root / spec.artifact_relpath)
        stale = STALE_BY_LABEL[spec.token_label]
        for rel in spec.token_files:
            path = root / rel
            raw = path.read_bytes()
            updated, count = tool._replace_sha_token_value(
                raw, spec.token_label, stale
            )
            assert count == 1
            assert current.encode("ascii") in raw
            path.write_bytes(updated)


def test_hash_refresh_check_is_read_only_on_pinned_repo_state() -> None:
    before = {rel: (tool.REPO_ROOT / rel).read_bytes() for rel in _relevant_paths()}
    assert tool.check_expected_hashes(repo_root=tool.REPO_ROOT) == []
    assert {rel: (tool.REPO_ROOT / rel).read_bytes() for rel in _relevant_paths()} == before


def test_hash_refresh_write_is_idempotent_in_temporary_tree_only(tmp_path: Path) -> None:
    repository_before = {
        rel: (tool.REPO_ROOT / rel).read_bytes() for rel in _relevant_paths()
    }
    _copy_relevant_tree(tmp_path)
    _make_all_tokens_stale(tmp_path)

    mismatches = tool.check_expected_hashes(repo_root=tmp_path)
    assert len(mismatches) == 8
    assert {item.identity_type for item in mismatches} == {
        "CANONICAL_ARTIFACT_SHA256"
    }
    assert len(tool.proposed_diff(repo_root=tmp_path, mismatches=mismatches)) > 0

    changed = tool.apply_updates(repo_root=tmp_path)
    assert set(changed) == {
        rel for spec in tool.DEFAULT_SPECS for rel in spec.token_files
    }
    assert tool.check_expected_hashes(repo_root=tmp_path) == []

    temporary_after_first_write = {
        rel: (tmp_path / rel).read_bytes() for rel in _relevant_paths()
    }
    assert tool.apply_updates(repo_root=tmp_path) == []
    assert {
        rel: (tmp_path / rel).read_bytes() for rel in _relevant_paths()
    } == temporary_after_first_write
    assert {
        rel: (tool.REPO_ROOT / rel).read_bytes() for rel in _relevant_paths()
    } == repository_before


def test_cli_refuses_repository_write_without_explicit_authorization() -> None:
    with pytest.raises(SystemExit) as exc_info:
        tool.main(["--mode", "write"])
    assert exc_info.value.code == 2
