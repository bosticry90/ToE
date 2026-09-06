from __future__ import annotations

import json
import subprocess
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
CURRENT_TARGET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CurrentTarget.lean"
)
CURRENT_AUTHORITY_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "CurrentAuthority.lean"
)


def _tracked(relative: str) -> bool:
    completed = subprocess.run(
        ["git", "ls-files", "--error-unmatch", "--", relative],
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
    )
    return completed.returncode == 0


def _module_path(module: str) -> str:
    return f"formal/toe_formal/{module.replace('.', '/')}.lean"


def test_thin_mirrors_are_derived_from_registry_target_and_evidence() -> None:
    registry = json.loads(REGISTRY_PATH.read_text(encoding="utf-8"))
    target = registry["CURRENT_LIVE_NEXT_TARGET_v0"]
    evidence = registry["CURRENT_LIVE_TARGET_EVIDENCE_v0"]
    evidence_module = evidence.removeprefix("formal/toe_formal/").removesuffix(
        ".lean"
    ).replace("/", ".")

    current_target = CURRENT_TARGET_PATH.read_text(encoding="utf-8")
    current_authority = CURRENT_AUTHORITY_PATH.read_text(encoding="utf-8")
    assert f"import {evidence_module}" in current_target
    assert f'"{target}"' in current_target
    assert f'"{target}"' in current_authority
    assert _tracked(evidence)


def test_thin_mirror_imports_resolve_only_to_committed_modules() -> None:
    for path in (CURRENT_TARGET_PATH, CURRENT_AUTHORITY_PATH):
        imports = [
            line.split(maxsplit=1)[1]
            for line in path.read_text(encoding="utf-8").splitlines()
            if line.startswith("import ToeFormal.")
        ]
        assert imports
        missing = [module for module in imports if not _tracked(_module_path(module))]
        assert not missing, f"thin mirror imports untracked modules: {missing}"
