from __future__ import annotations

from pathlib import Path
import subprocess

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
RECORDED_BASE = "75af1d110a57df26344ca151ccd26b9f5c1f7736"
CANONICAL_TEXT_SUFFIXES = {
    ".csv",
    ".flag",
    ".json",
    ".lean",
    ".log",
    ".md",
    ".py",
    ".sha256",
}


def _added_text_paths() -> list[str]:
    completed = subprocess.run(
        [
            "git",
            "diff",
            "--diff-filter=A",
            "--name-only",
            "-z",
            RECORDED_BASE,
            "HEAD",
        ],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
    )
    return sorted(
        path
        for path in completed.stdout.decode("utf-8").split("\0")
        if path and Path(path).suffix.lower() in CANONICAL_TEXT_SUFFIXES
    )


def _eol_attributes(paths: list[str]) -> dict[str, str]:
    observed: dict[str, str] = {}
    for start in range(0, len(paths), 64):
        completed = subprocess.run(
            ["git", "check-attr", "-z", "eol", "--", *paths[start : start + 64]],
            cwd=REPO_ROOT,
            check=True,
            capture_output=True,
        )
        fields = completed.stdout.decode("utf-8").split("\0")
        fields = fields[:-1] if fields and fields[-1] == "" else fields
        assert len(fields) % 3 == 0
        for index in range(0, len(fields), 3):
            path, attribute, value = fields[index : index + 3]
            assert attribute == "eol"
            observed[path] = value
    return observed


def test_added_integration_text_materializes_as_lf_in_clean_checkout() -> None:
    paths = _added_text_paths()
    assert len(paths) >= 600
    attributes = _eol_attributes(paths)
    assert set(attributes) == set(paths)
    assert {
        path: value for path, value in attributes.items() if value != "lf"
    } == {}
