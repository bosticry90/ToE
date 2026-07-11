from __future__ import annotations

import json
import subprocess
from pathlib import Path

import pytest

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))


def _strict_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate exact JSON key: {key}")
        result[key] = value
    return result


def _working_json_paths() -> list[Path]:
    completed = subprocess.run(
        [
            "git",
            "ls-files",
            "-z",
            "--cached",
            "--others",
            "--exclude-standard",
            "--",
            "*.json",
        ],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
    )
    return [
        REPO_ROOT / item.decode("utf-8", errors="strict")
        for item in completed.stdout.split(b"\0")
        if item and (REPO_ROOT / item.decode("utf-8", errors="strict")).exists()
    ]


def test_all_working_tree_json_files_are_utf8_strict_and_have_unique_exact_keys() -> None:
    paths = _working_json_paths()
    assert len(paths) >= 2500
    failures: list[str] = []
    for path in paths:
        try:
            text = path.read_text(encoding="utf-8", errors="strict")
            json.loads(text, object_pairs_hook=_strict_object)
        except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as error:
            failures.append(f"{path.relative_to(REPO_ROOT)}: {error}")
    assert not failures, "Tracked JSON integrity failures:\n- " + "\n- ".join(failures)


def test_strict_json_loader_negative_control_rejects_duplicate_keys() -> None:
    with pytest.raises(ValueError, match="duplicate exact JSON key: a"):
        json.loads('{"a": 1, "a": 2}', object_pairs_hook=_strict_object)
