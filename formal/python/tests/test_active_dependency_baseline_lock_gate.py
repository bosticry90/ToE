from __future__ import annotations

from importlib.metadata import version
from pathlib import Path

from packaging.version import Version
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
LOCK_PATH = REPO_ROOT / "requirements.active.lock"


MIN_SAFE_VERSIONS = {
    "cryptography": "46.0.6",
    "fonttools": "4.60.2",
    "pillow": "12.1.1",
}

MIN_SAFE_TOOLING_VERSIONS = {
    "pip": "26.0",
    "setuptools": "82.0.1",
}


def _parse_lock(path: Path) -> dict[str, str]:
    lines = path.read_text(encoding="utf-8").splitlines()
    parsed: dict[str, str] = {}
    for raw in lines:
        line = raw.strip()
        if not line or line.startswith("#") or "==" not in line:
            continue
        pkg, version = line.split("==", 1)
        parsed[pkg.lower()] = version
    return parsed


def test_active_dependency_lock_exists_and_is_nonempty() -> None:
    assert LOCK_PATH.exists(), f"Missing active dependency baseline lock: {LOCK_PATH}"
    assert LOCK_PATH.stat().st_size > 0, "Active dependency lockfile is empty"


def test_active_dependency_lock_is_pip_freeze_format() -> None:
    text = LOCK_PATH.read_text(encoding="utf-8").lstrip()
    assert not text.startswith("{"), (
        "Active dependency lockfile must be pip-freeze format, not JSON object format"
    )
    assert not text.startswith("["), (
        "Active dependency lockfile must be pip-freeze format, not JSON array format"
    )


def test_active_dependency_lock_has_minimum_safe_versions() -> None:
    locked = _parse_lock(LOCK_PATH)
    for pkg, min_safe in MIN_SAFE_VERSIONS.items():
        assert pkg in locked, f"Package missing from active lockfile: {pkg}"
        assert Version(locked[pkg]) >= Version(min_safe), (
            f"Package {pkg} is below minimum safe version in lockfile: "
            f"{locked[pkg]} < {min_safe}"
        )


def test_active_dependency_tooling_has_minimum_safe_versions() -> None:
    for pkg, min_safe in MIN_SAFE_TOOLING_VERSIONS.items():
        installed = version(pkg)
        assert Version(installed) >= Version(min_safe), (
            f"Installed tooling package {pkg} is below minimum safe version: "
            f"{installed} < {min_safe}"
        )
