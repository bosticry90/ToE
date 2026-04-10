from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

from formal.python.tools import governance_manifest_select as selector


EXPECTED_LEGACY_COUNT = 308
EXPECTED_LEGACY_SHA256 = "e9a04465630849abfb22cb09ae783135a03c8aec845186a6934d2fe5795e8026"
EXPECTED_FIRST_TEST = "formal/python/tests/test_active_dependency_baseline_lock_gate.py"
EXPECTED_LAST_TEST = "formal/python/tests/test_sql_integrity_snapshot_tool.py"


def _repo_root() -> Path:
    return selector.REPO_ROOT


def _manifest_path() -> Path:
    return _repo_root() / "formal" / "docs" / "release" / "GOVERNANCE_TEST_MANIFEST_v1.json"


def _governance_suite_path() -> Path:
    return _repo_root() / "governance_suite.ps1"


def _sha256_joined(items: list[str]) -> str:
    return hashlib.sha256("\n".join(items).encode("utf-8")).hexdigest()


def _extract_text_pinned_registry(content: str) -> list[str]:
    match = re.search(r"\$governanceGateTokenRegistry\s*=\s*@'\r?\n(.*?)\r?\n'@", content, flags=re.S)
    assert match is not None, "Could not locate text-pinned governance gate registry block in governance_suite.ps1."

    lines = [line.strip() for line in match.group(1).splitlines()]
    tests = [line for line in lines if line.startswith("formal/python/tests/test_") and line.endswith(".py")]
    assert tests, "Text-pinned governance gate registry must contain at least one test path."
    return tests


def test_governance_manifest_preserves_legacy_effective_selection_coverage() -> None:
    manifest_path = _manifest_path()
    payload = json.loads(manifest_path.read_text(encoding="utf-8"))

    group = payload["groups"]["governance_pytests"]
    tests, expected_count, expected_sha, _ = selector.load_manifest_tests(
        manifest_path, "governance_pytests"
    )

    assert expected_count == EXPECTED_LEGACY_COUNT, "Manifest expected_count drifted from legacy baseline."
    assert expected_sha == EXPECTED_LEGACY_SHA256, "Manifest expected_sha256 drifted from legacy baseline."

    assert len(tests) == EXPECTED_LEGACY_COUNT, "Manifest selected test count drifted from legacy baseline."
    assert _sha256_joined(tests) == EXPECTED_LEGACY_SHA256, "Manifest selected test hash drifted from legacy baseline."

    assert tests[0] == EXPECTED_FIRST_TEST, "Manifest first selected test drifted from legacy order."
    assert tests[-1] == EXPECTED_LAST_TEST, "Manifest last selected test drifted from legacy order."

    assert group["tests"] == tests, "Manifest test list order must remain deterministic."


def test_governance_text_pinned_registry_matches_manifest_and_disk() -> None:
    manifest_path = _manifest_path()
    tests, _, _, _ = selector.load_manifest_tests(manifest_path, "governance_pytests")

    suite_path = _governance_suite_path()
    suite_content = suite_path.read_text(encoding="utf-8")
    registry_tests = _extract_text_pinned_registry(suite_content)

    assert len(registry_tests) == len(set(registry_tests)), "Text-pinned governance gate registry contains duplicates."
    assert registry_tests == tests, (
        "Text-pinned governance gate registry must exactly match manifest order and contents."
    )

    missing = [test_path for test_path in registry_tests if not (_repo_root() / test_path).exists()]
    assert not missing, "Text-pinned governance registry references missing test file(s): " + ", ".join(missing)
