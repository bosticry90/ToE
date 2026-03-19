from __future__ import annotations

import re
import sys
from pathlib import Path

import pytest

from formal.python.meta.repo_environment import find_repo_root
from formal.python.meta.repo_environment import normalize_sys_path_entry


def _repo_root() -> Path:
    root = find_repo_root(Path(__file__))
    formal_python = root / "formal" / "python"
    if not formal_python.exists():
        raise RuntimeError(
            "Repo-root resolution failed: expected computed REPO_ROOT/formal/python to exist. "
            f"Computed REPO_ROOT={root}; __file__={Path(__file__).resolve()}"
        )

    expected_tests_dir = formal_python / "tests"
    assert expected_tests_dir.exists(), (
        "Repo-root resolution invariant failed; expected formal/python/tests at computed root: "
        f"{root}"
    )
    return root


def _norm_path_entry(entry: str) -> str:
    return normalize_sys_path_entry(entry)


def _enforce_sys_path_quarantine_invariants() -> None:
    root = _repo_root()
    root_norm = _norm_path_entry(str(root))
    archive_norm = _norm_path_entry(str(root / "archive"))

    normalized = [_norm_path_entry(p) for p in sys.path]
    if root_norm not in normalized:
        raise AssertionError("Repo root missing from sys.path")

    root_idx = normalized.index(root_norm)

    # Allowlist: in rare cases a test may temporarily prepend a path ahead of repo root
    # (e.g., for ephemeral module loading). This fixture is opt-in and should stay empty
    # in the canonical suite.
    allowed_prefixes = getattr(pytest, "_toe_sys_path_pre_root_allowlist", ())
    for idx, entry in enumerate(normalized[:root_idx]):
        if entry == "":
            continue
        if any(entry.startswith(_norm_path_entry(p)) for p in allowed_prefixes):
            continue
        # No restriction on other pre-root paths beyond the allowlist; we only require
        # that archive never appears and repo-root is present.

    if any(p == archive_norm or p.startswith(archive_norm + "\\") for p in normalized):
        raise AssertionError("Archive quarantine violation: archive path present in sys.path")


def pytest_configure():
    # Ensure the repo root is on sys.path so imports like `formal.python.*` work
    # regardless of the current working directory.
    root = str(_repo_root())
    if root not in sys.path:
        sys.path.insert(0, root)
    _enforce_sys_path_quarantine_invariants()


def pytest_runtest_setup(item):
    # Re-assert invariants before each test to catch late sys.path mutations.
    _enforce_sys_path_quarantine_invariants()


_QFT_EVOL_TRANCHE_DEPRECATED_PATTERN = re.compile(
    r"test_qft_evol_micro_tranche_01_(0[5-9]|[1-4][0-9]|5[0-1])_completeness_gate\.py"
)

def pytest_collection_modifyitems(config, items):
    for item in items:
        if _QFT_EVOL_TRANCHE_DEPRECATED_PATTERN.search(item.nodeid):
            item.add_marker(
                pytest.mark.skip(
                    reason="Deprecated tranche transition gate; saturation state is enforced by tranche 01_52."
                )
            )
            continue
