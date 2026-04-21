from __future__ import annotations

from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import qm_stat_reentry_downstream_governed_review_packet_report as tool


REPO_ROOT = find_repo_root(Path(__file__))
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_live_repo_qm_stat_reentry_downstream_governed_review_packet_is_ready() -> None:
    report = tool.build_report(packet_path=tool.DEFAULT_PACKET_PATH, captured_at_utc="2026-04-20T00:00:00Z")

    assert report["summary"]["terminal_outcome"] == "QM_STAT_DOWNSTREAM_GOVERNED_REVIEW_PACKET_READY"
    assert report["summary"]["packet_decision"] == "downstream_governed_review_packet_ready"
    assert report["summary"]["target_row_id"] == "ROW-SEAM-QM-STAT-001"
    assert report["summary"]["next_action"] == "EXECUTE_ONE_BOUNDED_QM_STAT_DOWNSTREAM_GOVERNED_REVIEW_USING_AUTHORED_PACKET_WITHOUT_CANONICAL_MUTATION"


def test_live_repo_qm_stat_reentry_downstream_governed_review_packet_preserves_noncanonical_boundary() -> None:
    report = tool.build_report(packet_path=tool.DEFAULT_PACKET_PATH, captured_at_utc="2026-04-20T00:00:00Z")

    assert report["criteria"]["promotion_policy_tokens_present"] is True
    assert report["criteria"]["canonical_boundary_tokens_present"] is True
    assert report["objective_quality"]["criteria"]["governed_review_not_yet_started"] is True
    assert report["summary"]["canonical_mutation_emitted"] is False


def test_live_repo_qm_stat_reentry_downstream_governed_review_packet_mirrors_are_cross_pinned() -> None:
    readme_text = _read(README_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    for ref in (
        "formal/docs/release/QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_PACKET_20260420_v0.md",
        "formal/python/tools/qm_stat_reentry_downstream_governed_review_packet_report.py",
        "formal/python/tests/test_qm_stat_reentry_downstream_governed_review_packet_report.py",
        "formal/output/reports/qm_stat_reentry_downstream_governed_review_packet_20260420_v0.json",
    ):
        assert ref in state_text
        assert ref in roadmap_text

    assert "QM_STAT_REENTRY_DOWNSTREAM_GOVERNED_REVIEW_PACKET_20260420_v0.md" in readme_text
    assert "test_qm_stat_reentry_downstream_governed_review_packet_report.py" in readme_text