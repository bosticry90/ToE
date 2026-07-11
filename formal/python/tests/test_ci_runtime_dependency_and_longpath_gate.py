from __future__ import annotations

import re
from pathlib import Path

import yaml

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
LOCK_PATH = REPO_ROOT / "requirements.ci.lock"
WORKFLOW_PATH = REPO_ROOT / ".github" / "workflows" / "ci.yml"


def _locked_packages() -> dict[str, str]:
    packages: dict[str, str] = {}
    for raw_line in LOCK_PATH.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#") or line.startswith("-r "):
            continue
        match = re.fullmatch(r"([A-Za-z0-9_.-]+)==([^\s]+)", line)
        assert match, f"CI requirement is not exactly pinned: {line}"
        packages[match.group(1).lower()] = match.group(2)
    return packages


def test_ci_runtime_dependencies_are_explicitly_pinned() -> None:
    text = LOCK_PATH.read_text(encoding="utf-8")
    assert "-r requirements.active.lock" in text
    packages = _locked_packages()
    assert {
        "cffi",
        "charset-normalizer",
        "colorama",
        "exceptiongroup",
        "iniconfig",
        "mpmath",
        "numpy",
        "packaging",
        "pdfminer.six",
        "pdfplumber",
        "pluggy",
        "pycparser",
        "pymupdf",
        "pypdfium2",
        "pygments",
        "pytest",
        "pyyaml",
        "scipy",
        "setuptools",
        "sympy",
        "tomli",
        "typing_extensions",
    } <= set(packages)
    assert packages["pytest"] == "9.0.3"


def test_ci_workflow_is_valid_yaml_and_installs_the_runtime_lock() -> None:
    workflow_text = WORKFLOW_PATH.read_text(encoding="utf-8")
    payload = yaml.safe_load(workflow_text)
    assert isinstance(payload, dict)
    assert isinstance(payload.get("jobs"), dict)

    install_commands = workflow_text.count("pip install -r requirements.ci.lock")
    python_jobs = workflow_text.count("python -m venv .venv")
    assert install_commands == python_jobs
    assert workflow_text.count("pip install --upgrade pip==26.0") == python_jobs
    assert "pip install --upgrade pip\n" not in workflow_text


def test_ci_checkout_enables_git_long_paths_before_actions_checkout() -> None:
    payload = yaml.safe_load(WORKFLOW_PATH.read_text(encoding="utf-8"))
    env = payload["env"]
    assert env == {
        "GIT_CONFIG_COUNT": "1",
        "GIT_CONFIG_KEY_0": "core.longpaths",
        "GIT_CONFIG_VALUE_0": "true",
    }
    workflow_text = WORKFLOW_PATH.read_text(encoding="utf-8")
    assert "formal.python.tools.lean_bounded_lake" in workflow_text
    assert "--jobs 1 --target ToeFormal --target ToeFormalAll" in workflow_text
    assert "lake build ToeFormalAll" not in workflow_text
    assert "lake env lean ToeFormalAll.lean" not in workflow_text
