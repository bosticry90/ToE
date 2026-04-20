from __future__ import annotations

from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.research import harder_qm_stat_target


REPO_ROOT = find_repo_root(Path(__file__))
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_research_mode_harder_qm_stat_target_materializes_live_row_local_witness() -> None:
    report = harder_qm_stat_target.build_harder_qm_stat_target_report()

    assert report["summary"]["terminal_outcome"] == "RESEARCH_MODE_HARDER_QM_STAT_TARGET_MATERIALIZED"
    assert report["summary"]["row_id"] == "ROW-SEAM-QM-STAT-001"
    assert report["summary"]["target_package_id"] == "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0"
    assert report["artifact"]["research_outcome"]["direct_math_artifact_v0"] is True


def test_research_mode_harder_qm_stat_target_metrics_are_bounded() -> None:
    report = harder_qm_stat_target.build_harder_qm_stat_target_report()
    metrics = report["artifact"]["metrics"]

    assert metrics["continuity_residual_sup_abs_max"] < 1.0e-6
    assert metrics["mass_drift_abs_max"] < 1.0e-6
    assert metrics["first_moment_transport_gap_abs_max"] < 1.0e-5
    assert metrics["second_moment_transport_gap_abs_max"] < 1.0e-4


def test_research_mode_harder_qm_stat_target_mirrors_are_cross_pinned() -> None:
    readme_text = _read(README_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    for ref in (
        "formal/docs/release/RESEARCH_MODE_HARDER_QM_STAT_TARGET_20260419_v0.md",
        "formal/python/research/harder_qm_stat_target.py",
        "formal/python/tests/test_research_mode_harder_qm_stat_target_report.py",
        "formal/output/research/research_qm_stat_transport_moment_stack_probe_20260419_v0.json",
        "formal/output/reports/research_mode_harder_qm_stat_target_20260419_v0.json",
    ):
        assert ref in state_text
        assert ref in roadmap_text

    assert "RESEARCH_MODE_HARDER_QM_STAT_TARGET_20260419_v0.md" in readme_text
    assert "test_research_mode_harder_qm_stat_target_report.py" in readme_text