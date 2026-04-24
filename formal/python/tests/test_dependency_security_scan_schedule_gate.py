from __future__ import annotations

from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCAN_SCRIPT_PATH = REPO_ROOT / "dependency_security_scan.ps1"
POLICY_PATH = REPO_ROOT / "formal" / "docs" / "security" / "DEPENDENCY_SECURITY_POLICY_v0.md"
LOCK_PATH = REPO_ROOT / "requirements.active.lock"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_dependency_scan_script_contract() -> None:
    text = _read(SCAN_SCRIPT_PATH)
    required_strings = [
        "pip_audit -r $lockPath",
        "$lockPath = \"requirements.active.lock\"",
        "dependency_security_scan_report_v0.json",
        "Dependency security scan failed",
        "report missing dependencies field",
    ]
    for marker in required_strings:
        assert marker in text, f"Scan script missing marker: {marker}"


def test_dependency_security_policy_contract() -> None:
    text = _read(POLICY_PATH)
    required_strings = [
        "Active dependency baseline is maintained in `requirements.active.lock`",
        "Run dependency security scan weekly",
        "test_active_dependency_baseline_lock_gate.py",
        "test_dependency_security_scan_schedule_gate.py",
    ]
    for marker in required_strings:
        assert marker in text, f"Policy missing marker: {marker}"


def test_dependency_lock_and_scan_surfaces_exist() -> None:
    assert LOCK_PATH.exists(), "Missing active dependency lockfile"
    assert SCAN_SCRIPT_PATH.exists(), "Missing dependency security scan script"
    assert POLICY_PATH.exists(), "Missing dependency security policy doc"


def test_dependency_lock_format_is_freeze_compatible() -> None:
    text = _read(LOCK_PATH).lstrip()
    assert not text.startswith("{"), "Active dependency lockfile must not be JSON object format"
    assert not text.startswith("["), "Active dependency lockfile must not be JSON array format"
