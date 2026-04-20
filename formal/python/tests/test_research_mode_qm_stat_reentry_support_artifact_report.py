from __future__ import annotations

from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import research_mode_qm_stat_reentry_support_artifact_report


REPO_ROOT = find_repo_root(Path(__file__))
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qm_stat_reentry_support_artifact_authorizes_one_bounded_queue_decision() -> None:
    report = research_mode_qm_stat_reentry_support_artifact_report.build_payload(
        declaration_path=research_mode_qm_stat_reentry_support_artifact_report.DEFAULT_DECLARATION_PATH,
        captured_at_utc="2026-04-19T00:00:00Z",
    )

    assert report["summary"]["terminal_outcome"] == "QM_STAT_REENTRY_SUPPORT_ARTIFACT_MATERIALIZED_AND_QUEUE_AUTHORIZED"
    assert report["summary"]["authorization_status"] == "AUTHORIZED_FOR_ONE_BOUNDED_REENTRY_QUEUE_DECISION"
    assert report["summary"]["next_action"] == "QUEUE_ONE_BOUNDED_QM_STAT_REENTRY_REVIEW_CYCLE"
    assert report["artifact"]["target_binding"]["authorized_candidate_target"] == "ROW-SEAM-QM-STAT-001::QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0"


def test_qm_stat_reentry_support_artifact_preserves_noncanonical_boundary() -> None:
    report = research_mode_qm_stat_reentry_support_artifact_report.build_payload(
        declaration_path=research_mode_qm_stat_reentry_support_artifact_report.DEFAULT_DECLARATION_PATH,
        captured_at_utc="2026-04-19T00:00:00Z",
    )

    assert report["criteria"]["eligibility_gap_targeted"] is True
    assert report["criteria"]["queue_authorization_ready"] is True
    assert report["summary"]["canonical_mutation_emitted"] is False


def test_qm_stat_reentry_support_artifact_mirrors_are_cross_pinned() -> None:
    readme_text = _read(README_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    for ref in (
        "formal/docs/release/RESEARCH_MODE_QM_STAT_REENTRY_SUPPORT_ARTIFACT_20260419_v0.json",
        "formal/python/tools/research_mode_qm_stat_reentry_support_artifact_report.py",
        "formal/python/tests/test_research_mode_qm_stat_reentry_support_artifact_report.py",
        "formal/output/reports/research_mode_qm_stat_reentry_support_artifact_20260419_v0.json",
        "formal/output/support/qm_stat_reentry_support_artifact_20260419_v0.json",
    ):
        assert ref in state_text
        assert ref in roadmap_text

    assert "RESEARCH_MODE_QM_STAT_REENTRY_SUPPORT_ARTIFACT_20260419_v0.json" in readme_text
    assert "test_research_mode_qm_stat_reentry_support_artifact_report.py" in readme_text