from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import governance_manifest_select as selector


EXPECTED_LEGACY_COUNT = 298
EXPECTED_LEGACY_SHA256 = "18e5424388060e770ba6b1acb626a27c0f437324614f16bd8b1f221655ccdcb2"
EXPECTED_FIRST_TEST = "formal/python/tests/test_active_dependency_baseline_lock_gate.py"
EXPECTED_LAST_TEST = "formal/python/tests/test_sql_integrity_snapshot_tool.py"


def _repo_root() -> Path:
    return selector.REPO_ROOT


def _manifest_path() -> Path:
    return _repo_root() / "formal" / "docs" / "release" / "GOVERNANCE_TEST_MANIFEST_v1.json"


def _sha256_joined(items: list[str]) -> str:
    return hashlib.sha256("\n".join(items).encode("utf-8")).hexdigest()


def test_governance_manifest_preserves_legacy_effective_selection_coverage() -> None:
    manifest_path = _manifest_path()
    payload = json.loads(manifest_path.read_text(encoding="utf-8"))

    group = payload["groups"]["governance_pytests"]
    tests, expected_count, expected_sha = selector.load_manifest_tests(manifest_path, "governance_pytests")

    assert expected_count == EXPECTED_LEGACY_COUNT, "Manifest expected_count drifted from legacy baseline."
    assert expected_sha == EXPECTED_LEGACY_SHA256, "Manifest expected_sha256 drifted from legacy baseline."

    assert len(tests) == EXPECTED_LEGACY_COUNT, "Manifest selected test count drifted from legacy baseline."
    assert _sha256_joined(tests) == EXPECTED_LEGACY_SHA256, "Manifest selected test hash drifted from legacy baseline."

    assert tests[0] == EXPECTED_FIRST_TEST, "Manifest first selected test drifted from legacy order."
    assert tests[-1] == EXPECTED_LAST_TEST, "Manifest last selected test drifted from legacy order."

    assert group["tests"] == tests, "Manifest test list order must remain deterministic."
