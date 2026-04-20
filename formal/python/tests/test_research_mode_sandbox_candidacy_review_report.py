from __future__ import annotations

from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.research import sandbox_candidacy_review


REPO_ROOT = find_repo_root(Path(__file__))
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_research_mode_sandbox_candidacy_review_accepts_qm_stat_seam_pilot() -> None:
    review = sandbox_candidacy_review.build_sandbox_candidacy_review()

    assert review["summary"]["terminal_outcome"] == "RESEARCH_MODE_SANDBOX_CANDIDACY_REVIEW_ACCEPTED"
    assert review["summary"]["selected_artifact_id"] == "research_qm_stat_transport_witness_probe_20260419_v0"
    assert review["summary"]["selected_target_binding"] == "ROW-SEAM-QM-STAT-001"
    assert review["summary"]["selected_candidate_class_v0"] == "SANDBOX_CANDIDATE_RESEARCH_ARTIFACT"


def test_research_mode_sandbox_candidacy_review_preserves_bridge_only_boundary() -> None:
    review = sandbox_candidacy_review.build_sandbox_candidacy_review()

    assert review["objective_quality"]["criteria"]["governance_bridge_ok"] is True
    assert (
        review["objective_quality"]["summary"]["bridge_limit_v0"]
        == "This review accepts sandbox candidacy only; it does not create a sandbox payload record or enter promotion review."
    )


def test_research_mode_sandbox_candidacy_review_mirrors_are_cross_pinned() -> None:
    readme_text = _read(README_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    for ref in (
        "formal/docs/release/RESEARCH_MODE_SANDBOX_CANDIDACY_REVIEW_20260419_v0.md",
        "formal/python/research/sandbox_candidacy_review.py",
        "formal/python/tests/test_research_mode_sandbox_candidacy_review_report.py",
        "formal/output/reports/research_mode_sandbox_candidacy_review_20260419_v0.json",
    ):
        assert ref in state_text
        assert ref in roadmap_text

    assert "RESEARCH_MODE_SANDBOX_CANDIDACY_REVIEW_20260419_v0.md" in readme_text
    assert "test_research_mode_sandbox_candidacy_review_report.py" in readme_text