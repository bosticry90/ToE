from __future__ import annotations

from pathlib import Path

from formal.python.meta.repo_environment import canonicalize_repo_paths


def test_repository_paths_are_serialized_relative_to_clone_root(tmp_path: Path) -> None:
    first = tmp_path / "clone-a"
    second = tmp_path / "clone-b"
    relative = Path("formal/python/toe/input.json")
    first_value = {"path": str(first / relative), "note": "unchanged"}
    second_value = {"path": str(second / relative), "note": "unchanged"}
    assert canonicalize_repo_paths(first_value, repo_root=first) == (
        canonicalize_repo_paths(second_value, repo_root=second)
    )
    assert canonicalize_repo_paths(first_value, repo_root=first)["path"] == (
        "formal/python/toe/input.json"
    )


def test_non_path_scientific_strings_are_never_rewritten(tmp_path: Path) -> None:
    value = {"latex": r"\psi_A", "label": r"sector\branch"}
    assert canonicalize_repo_paths(value, repo_root=tmp_path) == value
