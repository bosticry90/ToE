from __future__ import annotations

from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import research_mode_qm_stat_sandbox_review_execution_report


REPO_ROOT = find_repo_root(Path(__file__))
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qm_stat_sandbox_review_execution_completes_without_canonical_action() -> None:
    report = research_mode_qm_stat_sandbox_review_execution_report.build_report(
        captured_at_utc="2026-04-19T00:00:00Z"
    )

    assert report["summary"]["terminal_outcome"] == "QM_STAT_SANDBOX_REVIEW_COMPLETED_WITH_NO_CANONICAL_ACTION"
    assert report["summary"]["review_decision"] == "bounded_review_completed_with_no_canonical_action"
    assert report["summary"]["target_row_id"] == "ROW-SEAM-QM-STAT-001"
    assert report["summary"]["target_seam_id"] == "SEAM-QM-STAT"


def test_qm_stat_sandbox_review_execution_preserves_noncanonical_boundary() -> None:
    report = research_mode_qm_stat_sandbox_review_execution_report.build_report(
        captured_at_utc="2026-04-19T00:00:00Z"
    )

    assert report["criteria"]["payload_primary_object_preserved"] is True
    assert report["criteria"]["harder_target_preserved_as_support_only"] is True
    assert report["summary"]["canonical_mutation_emitted"] is False


def test_qm_stat_sandbox_review_execution_mirrors_are_cross_pinned() -> None:
    readme_text = _read(README_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    for ref in (
        "formal/python/tools/research_mode_qm_stat_sandbox_review_execution_report.py",
        "formal/python/tests/test_research_mode_qm_stat_sandbox_review_execution_report.py",
        "formal/output/reports/research_mode_qm_stat_sandbox_review_execution_20260419_v0.json",
    ):
        assert ref in state_text
        assert ref in roadmap_text

    assert "test_research_mode_qm_stat_sandbox_review_execution_report.py" in readme_text
    assert "research_mode_qm_stat_sandbox_review_execution_20260419_v0.json" in readme_text