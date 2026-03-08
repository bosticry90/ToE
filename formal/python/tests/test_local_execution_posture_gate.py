from __future__ import annotations

from pathlib import Path


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = _find_repo_root(Path(__file__))
GOVERNANCE_SUITE_PATH = REPO_ROOT / "governance_suite.ps1"


def test_governance_runs_local_orchestration_and_sql_snapshot() -> None:
    text = GOVERNANCE_SUITE_PATH.read_text(encoding="utf-8")
    assert "formal.python.orchestration.runner" in text
    assert "TOE_ASYNC_ORCHESTRATION_MANIFEST_v0.json" in text
    assert "formal.python.tools.sql_integrity_snapshot" in text
    assert "--fail-on-issues" in text


def test_governance_enforces_rust_execution_posture() -> None:
    text = GOVERNANCE_SUITE_PATH.read_text(encoding="utf-8")
    assert "Get-Command cargo" in text
    assert "cargo run --manifest-path formal/rust/toe_trust_core/Cargo.toml" in text
    assert "TOE_REQUIRE_RUST_LOCAL" in text
