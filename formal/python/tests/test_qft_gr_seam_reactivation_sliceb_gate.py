from __future__ import annotations

from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
BRIEF_PATH = REPO_ROOT / "formal" / "docs" / "release" / "QFT_GR_SEAM_REACTIVATION_SLICEB_AUTHORIZATION_BRIEF_v0.md"
PACKET_PATH = REPO_ROOT / "formal" / "docs" / "release" / "QFT_GR_SEAM_REACTIVATION_SLICEB_BOUNDED_EXECUTION_PACKET_v0.md"
ASSESS_PATH = REPO_ROOT / "formal" / "docs" / "release" / "QFT_GR_SEAM_REACTIVATION_SLICEB_ASSESSMENT_NOTE_v0.md"
OBJECTIVE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_v0.md"

REQUIRED_QUESTION = "stress_energy_to_weak_curvature_handoff_strengthening"
REQUIRED_HOLD_TOKEN = "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_sliceb_artifacts_exist() -> None:
    for p in (BRIEF_PATH, PACKET_PATH, ASSESS_PATH):
        assert p.exists(), f"Missing Slice B artifact: {p}"


def test_sliceb_artifacts_anchor_objective_and_question() -> None:
    objective_text = _read(OBJECTIVE_PATH)
    assert REQUIRED_QUESTION in objective_text

    for path in (BRIEF_PATH, PACKET_PATH, ASSESS_PATH):
        text = _read(path)
        assert "formal/docs/paper/TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_v0.md" in text
        assert REQUIRED_QUESTION in text


def test_sliceb_invariance_and_nonclaim_markers() -> None:
    brief = _read(BRIEF_PATH)
    packet = _read(PACKET_PATH)
    assess = _read(ASSESS_PATH)

    assert REQUIRED_HOLD_TOKEN in brief
    assert REQUIRED_HOLD_TOKEN in packet

    for text in (brief, packet, assess):
        assert "does not claim seam closure" in text
        assert "does not claim QFT-GR unification completeness" in text

    assert "does not lift Packet42 hold" in brief
    assert "does not authorize packet42 hold release" in packet
    assert "does not lift Packet42 hold" in assess


def test_sliceb_status_tokens_present() -> None:
    brief = _read(BRIEF_PATH)
    packet = _read(PACKET_PATH)
    assess = _read(ASSESS_PATH)

    assert "QFT_GR_SEAM_REACTIVATION_SLICEB_STATUS_v0: AUTHORIZED_BOUNDED_EXECUTION_PENDING" in brief
    assert "QFT_GR_SEAM_REACTIVATION_SLICEB_EXECUTION_STATUS_v0: EXECUTED_BOUNDED_v0" in packet
    assert "QFT_GR_SEAM_REACTIVATION_SLICEB_ASSESSMENT_STATUS_v0: ASSESSED_BOUNDED_v0" in assess
