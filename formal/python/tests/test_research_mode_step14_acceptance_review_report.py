from __future__ import annotations

from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.research import acceptance_review


REPO_ROOT = find_repo_root(Path(__file__))
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_research_mode_step14_acceptance_review_passes_bounded_criteria() -> None:
    review = acceptance_review.build_acceptance_review()

    assert review["summary"]["terminal_outcome"] == "RESEARCH_MODE_STEP14_ACCEPTANCE_REVIEW_PASSED_BOUNDED"
    assert review["summary"]["step_14_status_v0"] == "COMPLETE_BOUNDED_v0_NONCLAIM"
    assert review["objective_quality"]["criteria"]["artifact_quality_ok"] is True
    assert review["objective_quality"]["criteria"]["boundary_integrity_ok"] is True
    assert review["objective_quality"]["criteria"]["loop_compression_ok"] is True
    assert review["objective_quality"]["criteria"]["repeatability_ok"] is True


def test_research_mode_step14_acceptance_review_marks_bounded_proxy_basis_explicitly() -> None:
    review = acceptance_review.build_acceptance_review()

    assert review["criteria"]["loop_compression"]["status_v0"] == "PASS_BOUNDED_PROXY"
    assert review["criteria"]["repeatability"]["status_v0"] == "PASS_BOUNDED_PROXY"
    assert (
        review["objective_quality"]["summary"]["bounded_limit_v0"]
        == "This review accepts bounded proxy evidence for loop compression and repeatability, not a historical time-study or longitudinal multi-pack audit."
    )


def test_research_mode_step14_acceptance_review_mirrors_are_cross_pinned() -> None:
    readme_text = _read(README_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    for ref in (
        "formal/docs/release/RESEARCH_MODE_STEP14_ACCEPTANCE_REVIEW_20260419_v0.md",
        "formal/python/research/acceptance_review.py",
        "formal/python/tests/test_research_mode_step14_acceptance_review_report.py",
        "formal/output/reports/research_mode_step14_acceptance_review_20260419_v0.json",
    ):
        assert ref in state_text
        assert ref in roadmap_text

    assert "RESEARCH_MODE_STEP14_ACCEPTANCE_REVIEW_20260419_v0.md" in readme_text
    assert "test_research_mode_step14_acceptance_review_report.py" in readme_text