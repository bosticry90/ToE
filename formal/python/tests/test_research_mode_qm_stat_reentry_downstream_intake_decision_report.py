from __future__ import annotations

from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import research_mode_qm_stat_reentry_downstream_intake_decision_report


REPO_ROOT = find_repo_root(Path(__file__))
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qm_stat_reentry_downstream_intake_accepts_packet_for_bounded_execution_packet_authoring() -> None:
    report = research_mode_qm_stat_reentry_downstream_intake_decision_report.build_report(
        declaration_path=research_mode_qm_stat_reentry_downstream_intake_decision_report.DEFAULT_DECLARATION_PATH,
        captured_at_utc="2026-04-20T00:00:00Z",
    )

    assert report["summary"]["terminal_outcome"] == "QM_STAT_REENTRY_DOWNSTREAM_INTAKE_ACCEPTED_FOR_BOUNDED_EXECUTION_PACKET_AUTHORING"
    assert report["summary"]["intake_decision"] == "reentry_intake_accepted_for_bounded_execution_packet_authoring"
    assert report["summary"]["target_row_id"] == "ROW-SEAM-QM-STAT-001"
    assert report["summary"]["next_action"] == "AUTHOR_ONE_BOUNDED_QM_STAT_REENTRY_REVIEW_EXECUTION_PACKET_WITHOUT_CANONICAL_MUTATION"


def test_qm_stat_reentry_downstream_intake_preserves_noncanonical_boundary() -> None:
    report = research_mode_qm_stat_reentry_downstream_intake_decision_report.build_report(
        declaration_path=research_mode_qm_stat_reentry_downstream_intake_decision_report.DEFAULT_DECLARATION_PATH,
        captured_at_utc="2026-04-20T00:00:00Z",
    )

    assert report["criteria"]["packet_ready_for_intake"] is True
    assert report["criteria"]["target_binding_preserved"] is True
    assert report["objective_quality"]["criteria"]["handoff_boundary_consumed_without_execution"] is True
    assert report["summary"]["canonical_mutation_emitted"] is False


def test_qm_stat_reentry_downstream_intake_mirrors_are_cross_pinned() -> None:
    readme_text = _read(README_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    for ref in (
        "formal/docs/release/RESEARCH_MODE_QM_STAT_REENTRY_DOWNSTREAM_INTAKE_DECISION_20260420_v0.md",
        "formal/docs/release/RESEARCH_MODE_QM_STAT_REENTRY_DOWNSTREAM_INTAKE_DECISION_20260420_v0.json",
        "formal/python/tools/research_mode_qm_stat_reentry_downstream_intake_decision_report.py",
        "formal/python/tests/test_research_mode_qm_stat_reentry_downstream_intake_decision_report.py",
        "formal/output/reports/research_mode_qm_stat_reentry_downstream_intake_decision_20260420_v0.json",
    ):
        assert ref in state_text
        assert ref in roadmap_text

    assert "RESEARCH_MODE_QM_STAT_REENTRY_DOWNSTREAM_INTAKE_DECISION_20260420_v0.md" in readme_text
    assert "test_research_mode_qm_stat_reentry_downstream_intake_decision_report.py" in readme_text