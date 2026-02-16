from __future__ import annotations

from pathlib import Path

from formal.python.tests.test_ct08_files_do_not_contain_ct07_tokens import CT08_FILES


def _discover_ct08_lane_files(repo_root: Path) -> set[str]:
    patterns = [
        "formal/python/toe/comparators/ct08_*.py",
        "formal/python/tools/ct08_*.py",
        "formal/python/tests/test_ct08_*.py",
        "formal/docs/programs/CT08_*.md",
        "formal/docs/ct08_*.md",
        "formal/external_evidence/ct08_external_anchor_dispersion_highk_domain_01/*",
        "formal/markdown/locks/observables/CT-08_*.md",
    ]

    discovered: set[str] = set()
    for pattern in patterns:
        for path in repo_root.glob(pattern):
            if path.is_file():
                discovered.add(path.relative_to(repo_root).as_posix())

    excluded = {
        "formal/python/tests/test_ct08_files_do_not_contain_ct07_tokens.py",
        "formal/python/tests/test_ct08_file_enumerator_guard_coverage.py",
    }
    return discovered - excluded


def test_ct08_file_list_guard_covers_discovered_lane_files() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    discovered = _discover_ct08_lane_files(repo_root)
    listed = set(CT08_FILES)

    missing_in_guard = sorted(discovered - listed)
    stale_in_guard = sorted(listed - discovered)

    assert not missing_in_guard, (
        "CT-08 guard list is missing discovered lane files:\n" + "\n".join(missing_in_guard)
    )
    assert not stale_in_guard, (
        "CT-08 guard list contains stale paths not present on disk:\n" + "\n".join(stale_in_guard)
    )
