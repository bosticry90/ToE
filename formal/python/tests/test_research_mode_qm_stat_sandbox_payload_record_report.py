from __future__ import annotations

from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.research import qm_stat_sandbox_payload_record


REPO_ROOT = find_repo_root(Path(__file__))
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qm_stat_sandbox_payload_record_materializes_promotion_entry_shape() -> None:
    payload = qm_stat_sandbox_payload_record.build_qm_stat_sandbox_payload_record()

    assert payload["summary"]["terminal_outcome"] == "RESEARCH_MODE_QM_STAT_SANDBOX_PAYLOAD_RECORD_MATERIALIZED"
    assert payload["metadata_record"]["artifact_class"] == "PROMOTION_CANDIDATE_SANDBOX_ARTIFACT"
    assert payload["target_binding"]["row_id"] == "ROW-SEAM-QM-STAT-001"
    assert payload["target_binding"]["seam_id"] == "SEAM-QM-STAT"
    assert payload["decision_boundary"] == "PROMOTE_PLUS_HOLD_PLUS_REJECT_ONLY"


def test_qm_stat_sandbox_payload_record_preserves_bounded_nonpromotion_boundary() -> None:
    payload = qm_stat_sandbox_payload_record.build_qm_stat_sandbox_payload_record()

    assert payload["objective_quality"]["criteria"]["accepted_candidacy_ok"] is True
    assert (
        payload["objective_quality"]["summary"]["payload_limit_v0"]
        == "This payload record prepares one bounded QM-STAT witness for possible governed review entry only; it does not itself enter governed review or emit canonical mutation."
    )


def test_qm_stat_sandbox_payload_record_mirrors_are_cross_pinned() -> None:
    readme_text = _read(README_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    for ref in (
        "formal/docs/release/RESEARCH_MODE_QM_STAT_SANDBOX_PAYLOAD_RECORD_20260419_v0.md",
        "formal/python/research/qm_stat_sandbox_payload_record.py",
        "formal/python/tests/test_research_mode_qm_stat_sandbox_payload_record_report.py",
        "formal/output/sandbox/qm_stat_transport_witness_sandbox_artifact_20260419_v0.json",
        "formal/output/reports/research_mode_qm_stat_sandbox_payload_record_20260419_v0.json",
    ):
        assert ref in state_text
        assert ref in roadmap_text

    assert "RESEARCH_MODE_QM_STAT_SANDBOX_PAYLOAD_RECORD_20260419_v0.md" in readme_text
    assert "test_research_mode_qm_stat_sandbox_payload_record_report.py" in readme_text