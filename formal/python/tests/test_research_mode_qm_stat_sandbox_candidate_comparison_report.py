from __future__ import annotations

from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.research import qm_stat_sandbox_candidate_comparison


REPO_ROOT = find_repo_root(Path(__file__))
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qm_stat_sandbox_candidate_comparison_aligns_payload_and_harder_target() -> None:
    report = qm_stat_sandbox_candidate_comparison.build_qm_stat_sandbox_candidate_comparison()

    assert report["summary"]["terminal_outcome"] == "RESEARCH_MODE_QM_STAT_SANDBOX_CANDIDATE_COMPARISON_ALIGNED"
    assert report["summary"]["row_id"] == "ROW-SEAM-QM-STAT-001"
    assert report["summary"]["seam_id"] == "SEAM-QM-STAT"
    assert report["summary"]["target_package_id"] == "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0"


def test_qm_stat_sandbox_candidate_comparison_keeps_harder_target_as_support_only() -> None:
    report = qm_stat_sandbox_candidate_comparison.build_qm_stat_sandbox_candidate_comparison()

    assert report["objective_quality"]["criteria"]["support_role_ok"] is True
    assert (
        report["objective_quality"]["summary"]["comparison_limit_v0"]
        == "The harder live target is comparison evidence only. The payload record remains the governed-entry object; the harder target does not become a silent payload substitute."
    )


def test_qm_stat_sandbox_candidate_comparison_mirrors_are_cross_pinned() -> None:
    readme_text = _read(README_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    for ref in (
        "formal/docs/release/RESEARCH_MODE_QM_STAT_SANDBOX_CANDIDATE_COMPARISON_20260419_v0.md",
        "formal/python/research/qm_stat_sandbox_candidate_comparison.py",
        "formal/python/tests/test_research_mode_qm_stat_sandbox_candidate_comparison_report.py",
        "formal/output/reports/research_mode_qm_stat_sandbox_candidate_comparison_20260419_v0.json",
    ):
        assert ref in state_text
        assert ref in roadmap_text

    assert "RESEARCH_MODE_QM_STAT_SANDBOX_CANDIDATE_COMPARISON_20260419_v0.md" in readme_text
    assert "test_research_mode_qm_stat_sandbox_candidate_comparison_report.py" in readme_text