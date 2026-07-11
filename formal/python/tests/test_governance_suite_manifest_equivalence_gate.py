from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import governance_manifest_select as selector


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


def test_governance_manifest_selection_is_deterministic_and_contract_valid() -> None:
    manifest_path = _manifest_path()
    payload = json.loads(manifest_path.read_text(encoding="utf-8"))

    group = payload["groups"]["governance_pytests"]
    tests, expected_count, expected_sha, _ = selector.load_manifest_tests(
        manifest_path, "governance_pytests"
    )

    assert expected_count == group["expected_count"], "Manifest expected_count must match selector contract."
    assert expected_sha == group["expected_sha256"], "Manifest expected_sha256 must match selector contract."

    assert len(tests) == expected_count, "Selector output count must match expected_count."
    assert _sha256_joined(tests) == expected_sha, "Selector output hash must match expected_sha256."

    assert tests[0] == EXPECTED_FIRST_TEST, "Manifest first selected test drifted from legacy order."
    assert tests[-1] == EXPECTED_LAST_TEST, "Manifest last selected test drifted from legacy order."

    assert group["tests"] == tests, "Manifest test list order must remain deterministic."


def test_ci_governance_groups_have_enforced_count_and_hash_contracts() -> None:
    manifest_path = _manifest_path()
    payload = json.loads(manifest_path.read_text(encoding="utf-8"))
    for group_name in ("critical_gates", "integrity_gates"):
        group = payload["groups"][group_name]
        tests, expected_count, expected_sha, _ = selector.load_manifest_tests(
            manifest_path, group_name
        )
        assert expected_count == len(tests) == group["expected_count"]
        assert expected_sha == _sha256_joined(tests) == group["expected_sha256"]


def test_governance_suite_is_manifest_authoritative_single_source() -> None:
    manifest_path = _manifest_path()
    tests, _, _, _ = selector.load_manifest_tests(manifest_path, "governance_pytests")

    suite_path = _governance_suite_path()
    suite_content = suite_path.read_text(encoding="utf-8")

    assert "$governanceGateTokenRegistry" not in suite_content, (
        "governance_suite.ps1 must not maintain a text-pinned registry once manifest-authoritative mode is enabled."
    )
    assert "Resolve-GovernanceManifestGroup" in suite_content
    assert "governance_manifest_select" in suite_content

    missing = [test_path for test_path in tests if not (_repo_root() / test_path).exists()]
    assert not missing, "Manifest governance selection references missing test file(s): " + ", ".join(missing)
