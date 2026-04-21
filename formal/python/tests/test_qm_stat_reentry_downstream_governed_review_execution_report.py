from __future__ import annotations

from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import qm_stat_reentry_downstream_governed_review_execution_report as tool


REPO_ROOT = find_repo_root(Path(__file__))
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_live_repo_qm_stat_reentry_downstream_governed_review_execution_completes_nonlive() -> None:
    report = tool.build_report(declaration_path=tool.DEFAULT_DECLARATION_PATH, captured_at_utc="2026-04-20T00:00:00Z")

    assert report["summary"]["terminal_outcome"] == "QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_EXECUTED_NONLIVE"
    assert report["summary"]["target_row_id"] == "ROW-SEAM-QM-STAT-001"
    assert report["summary"]["target_seam_id"] == "SEAM-QM-STAT"
    assert report["summary"]["next_action"] == "STOP_AT_QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_EXECUTION_TOKEN_PENDING_ANY_FURTHER_GOVERNANCE_AUTHORIZATION"


def test_live_repo_qm_stat_reentry_downstream_governed_review_execution_preserves_noncanonical_boundary() -> None:
    report = tool.build_report(declaration_path=tool.DEFAULT_DECLARATION_PATH, captured_at_utc="2026-04-20T00:00:00Z")

    assert report["criteria"]["packet_ready"] is True
    assert report["criteria"]["target_binding_preserved"] is True
    assert report["criteria"]["canonical_action_boundary_present"] is True
    assert report["summary"]["canonical_mutation_emitted"] is False


def test_live_repo_qm_stat_reentry_downstream_governed_review_execution_mirrors_are_cross_pinned() -> None:
    readme_text = _read(README_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    for ref in (
        "formal/docs/release/QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_EXECUTION_20260420_v0.json",
        "formal/python/tools/qm_stat_reentry_downstream_governed_review_execution_report.py",
        "formal/python/tests/test_qm_stat_reentry_downstream_governed_review_execution_report.py",
        "formal/output/reports/qm_stat_reentry_downstream_governed_review_execution_20260420_v0.json",
    ):
        assert ref in state_text
        assert ref in roadmap_text

    assert "QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_EXECUTION_20260420_v0.json" in readme_text
    assert "test_qm_stat_reentry_downstream_governed_review_execution_report.py" in readme_text