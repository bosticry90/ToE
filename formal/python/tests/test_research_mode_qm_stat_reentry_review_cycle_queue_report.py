from __future__ import annotations

from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import research_mode_qm_stat_reentry_review_cycle_queue_report


REPO_ROOT = find_repo_root(Path(__file__))
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qm_stat_reentry_review_cycle_queue_materializes_queue_ready_route() -> None:
    report = research_mode_qm_stat_reentry_review_cycle_queue_report.build_payload(
        declaration_path=research_mode_qm_stat_reentry_review_cycle_queue_report.DEFAULT_DECLARATION_PATH,
        captured_at_utc="2026-04-19T00:00:00Z",
    )

    assert report["summary"]["terminal_outcome"] == "QM_STAT_REENTRY_REVIEW_CYCLE_QUEUED_FOR_ONE_BOUNDED_REVIEW"
    assert report["summary"]["queue_status"] == "QUEUED_FOR_ONE_BOUNDED_REENTRY_REVIEW_CYCLE"
    assert report["summary"]["queue_packet_status"] == "PENDING_REENTRY_QUEUE_PACKET_AUTHORING"
    assert report["summary"]["next_action"] == "AUTHOR_ONE_BOUNDED_QM_STAT_REENTRY_REVIEW_QUEUE_PACKET"


def test_qm_stat_reentry_review_cycle_queue_preserves_noncanonical_boundary() -> None:
    report = research_mode_qm_stat_reentry_review_cycle_queue_report.build_payload(
        declaration_path=research_mode_qm_stat_reentry_review_cycle_queue_report.DEFAULT_DECLARATION_PATH,
        captured_at_utc="2026-04-19T00:00:00Z",
    )

    assert report["criteria"]["eligibility_ready_for_queue"] is True
    assert report["criteria"]["support_artifact_ready_for_queue"] is True
    assert report["summary"]["canonical_mutation_emitted"] is False


def test_qm_stat_reentry_review_cycle_queue_mirrors_are_cross_pinned() -> None:
    readme_text = _read(README_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    for ref in (
        "formal/docs/release/RESEARCH_MODE_QM_STAT_REENTRY_REVIEW_CYCLE_QUEUE_20260419_v0.json",
        "formal/python/tools/research_mode_qm_stat_reentry_review_cycle_queue_report.py",
        "formal/python/tests/test_research_mode_qm_stat_reentry_review_cycle_queue_report.py",
        "formal/output/reports/research_mode_qm_stat_reentry_review_cycle_queue_20260419_v0.json",
        "formal/output/queue/qm_stat_reentry_review_cycle_queue_20260419_v0.json",
    ):
        assert ref in state_text
        assert ref in roadmap_text

    assert "RESEARCH_MODE_QM_STAT_REENTRY_REVIEW_CYCLE_QUEUE_20260419_v0.json" in readme_text
    assert "test_research_mode_qm_stat_reentry_review_cycle_queue_report.py" in readme_text