from __future__ import annotations

import subprocess
from pathlib import Path

import tomli
import yaml

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))


def _working_paths(*patterns: str) -> list[Path]:
    completed = subprocess.run(
        [
            "git",
            "ls-files",
            "-z",
            "--cached",
            "--others",
            "--exclude-standard",
            "--",
            *patterns,
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


def test_all_working_tree_yaml_files_parse_as_utf8() -> None:
    paths = _working_paths("*.yml", "*.yaml")
    assert len(paths) >= 5
    failures: list[str] = []
    for path in paths:
        try:
            yaml.safe_load(path.read_text(encoding="utf-8", errors="strict"))
        except (UnicodeDecodeError, yaml.YAMLError) as error:
            failures.append(f"{path.relative_to(REPO_ROOT)}: {error}")
    assert not failures, "Tracked YAML integrity failures:\n- " + "\n- ".join(failures)


def test_aristotle_claim_registry_preserves_table_as_valid_literal_data() -> None:
    path = REPO_ROOT / "formal" / "aristotle" / "claim_registry.yaml"
    payload = yaml.safe_load(path.read_text(encoding="utf-8"))
    table = payload["compilation_gates"]
    assert isinstance(table, str)
    assert "| Gate Order | file_id |" in table
    assert "ToeFormal.Derivation.Conventions.FourierSymbols" in table


def test_all_working_tree_toml_files_parse_as_utf8() -> None:
    paths = _working_paths("*.toml")
    assert len(paths) >= 4
    failures: list[str] = []
    for path in paths:
        try:
            tomli.loads(path.read_text(encoding="utf-8", errors="strict"))
        except (UnicodeDecodeError, tomli.TOMLDecodeError) as error:
            failures.append(f"{path.relative_to(REPO_ROOT)}: {error}")
    assert not failures, "Tracked TOML integrity failures:\n- " + "\n- ".join(failures)
