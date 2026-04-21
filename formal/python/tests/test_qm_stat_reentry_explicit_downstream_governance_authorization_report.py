from __future__ import annotations

from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import qm_stat_reentry_explicit_downstream_governance_authorization_report as tool


REPO_ROOT = find_repo_root(Path(__file__))
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_live_repo_qm_stat_reentry_explicit_downstream_governance_authorization() -> None:
    report = tool.build_report(declaration_path=tool.DEFAULT_DECLARATION_PATH, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "QM_STAT_REENTRY_SINGLE_GOVERNED_REVIEW_PATH_AUTHORIZED_NONLIVE_v0"
    assert report["summary"]["authorization_scope_token"] == "CONTROL_SURFACE_QM_STAT_REENTRY_DOWNSTREAM_GOVERNANCE_AUTHORIZATION_NONLIVE"
    assert report["summary"]["next_action"] == "AUTHOR_ONE_BOUNDED_QM_STAT_DOWNSTREAM_GOVERNED_REVIEW_PACKET_WITHOUT_CANONICAL_MUTATION"


def test_live_repo_qm_stat_reentry_downstream_governance_authorization_preserves_noncanonical_boundary() -> None:
    report = tool.build_report(declaration_path=tool.DEFAULT_DECLARATION_PATH, captured_at_utc=None)

    assert report["criteria"]["promotion_policy_tokens_present"] is True
    assert report["criteria"]["canonical_boundary_tokens_present"] is True
    assert report["objective_quality"]["criteria"]["canonical_mutation_withheld"] is True
    assert report["summary"]["canonical_mutation_emitted"] is False


def test_live_repo_qm_stat_reentry_downstream_governance_authorization_mirrors_are_cross_pinned() -> None:
    readme_text = _read(README_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    for ref in (
        "formal/docs/release/QM_STAT_REENTRY_EXPLICIT_DOWNSTREAM_GOVERNANCE_AUTHORIZATION_20260420_v0.json",
        "formal/python/tools/qm_stat_reentry_explicit_downstream_governance_authorization_report.py",
        "formal/python/tests/test_qm_stat_reentry_explicit_downstream_governance_authorization_report.py",
        "formal/output/reports/qm_stat_reentry_explicit_downstream_governance_authorization_20260420_v0.json",
    ):
        assert ref in state_text
        assert ref in roadmap_text

    assert "QM_STAT_REENTRY_EXPLICIT_DOWNSTREAM_GOVERNANCE_AUTHORIZATION_20260420_v0.json" in readme_text
    assert "test_qm_stat_reentry_explicit_downstream_governance_authorization_report.py" in readme_text