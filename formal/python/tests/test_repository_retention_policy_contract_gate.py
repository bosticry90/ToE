from __future__ import annotations

from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
POLICY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "REPOSITORY_RETENTION_POLICY_v0.md"
SUITE_PATH = REPO_ROOT / "governance_suite.ps1"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_retention_policy_contract_tokens_are_present() -> None:
    text = _read(POLICY_PATH)
    required_tokens = [
        "REPOSITORY_RETENTION_POLICY_v0",
        "RETENTION_SCOPE_SCRATCH_v0: SHORT_LIVED_WORK_ARTIFACTS",
        "RETENTION_SCOPE_TOOLING_SNAPSHOTS_v0: TRANSITIONAL_PIPELINE_EVIDENCE",
        "RETENTION_SCOPE_BACKUP_v0: DATED_CANONICAL_BACKUPS",
        "RETENTION_SCOPE_ARCHIVE_v0: FROZEN_LEGACY_REFERENCE",
        "RETENTION_POLICY_GOVERNANCE_GATE_v0: formal/python/tests/test_repository_retention_policy_contract_gate.py",
        "scratch/",
        "formal/tooling_snapshots/",
        "backup/",
        "archive/",
        "30-day cadence",
        "60-day cadence",
        "90-day cadence",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "Repository retention policy token drift: " + ", ".join(missing)


def test_retention_policy_paths_exist() -> None:
    required_dirs = [
        REPO_ROOT / "scratch",
        REPO_ROOT / "formal" / "tooling_snapshots",
        REPO_ROOT / "backup",
        REPO_ROOT / "archive",
    ]
    missing = [str(path.relative_to(REPO_ROOT)) for path in required_dirs if not path.exists()]
    assert not missing, "Retention policy references missing directory(ies): " + ", ".join(missing)


def test_governance_suite_executes_retention_policy_gate() -> None:
    suite_text = _read(SUITE_PATH)
    gate_relpath = "formal/python/tests/test_repository_retention_policy_contract_gate.py"
    assert gate_relpath in suite_text, "governance_suite.ps1 must execute the repository retention policy gate."
