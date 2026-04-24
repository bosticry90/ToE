from __future__ import annotations

from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
INCREMENT15_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT15_EXECUTION_PACKET_v0.md"
)
INCREMENT15_ASSESS_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT15_ASSESSMENT_NOTE_v0.md"
)
DECISION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT15_SEMANTIC_DELTA_DECISION_NOTE_v0.md"
)
PARENT_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SEAM_REACTIVATION_SLICEB_BOUNDED_EXECUTION_PACKET_v0.md"
)
OBJECTIVE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_v0.md"

REQUIRED_QUESTION = "stress_energy_to_weak_curvature_handoff_strengthening"
REQUIRED_HOLD_TOKEN = "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_sliceb_increment15_artifacts_exist() -> None:
    for p in (INCREMENT15_PACKET_PATH, INCREMENT15_ASSESS_PATH):
        assert p.exists(), f"Missing Slice B Increment15 artifact: {p}"


def test_sliceb_increment15_anchor_and_delta_parity() -> None:
    objective = _read(OBJECTIVE_PATH)
    parent = _read(PARENT_PACKET_PATH)
    decision = _read(DECISION_PATH)
    packet = _read(INCREMENT15_PACKET_PATH)
    assess = _read(INCREMENT15_ASSESS_PATH)

    assert REQUIRED_QUESTION in objective
    assert REQUIRED_QUESTION in parent
    assert REQUIRED_QUESTION in decision

    for text in (packet, assess):
        assert "formal/docs/paper/TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_v0.md" in text
        assert "formal/docs/release/QFT_GR_SEAM_REACTIVATION_SLICEB_BOUNDED_EXECUTION_PACKET_v0.md" in text
        assert REQUIRED_QUESTION in text

    assert "formal/docs/release/QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT15_SEMANTIC_DELTA_DECISION_NOTE_v0.md" in packet
    assert "controlled augmentation" in packet
    assert "less-admissible outcome" in packet
    assert "strengthening-monotonicity failure" in packet


def test_sliceb_increment15_invariance_and_nonclaim_markers() -> None:
    packet = _read(INCREMENT15_PACKET_PATH)
    assess = _read(INCREMENT15_ASSESS_PATH)

    assert REQUIRED_HOLD_TOKEN in packet
    assert "SCALAR_FREEZE_INVARIANCE_v0: ENFORCED" in packet
    assert "WORKFLOW_CLOSURE_INVARIANCE_v0: ENFORCED" in packet
    assert "GR_QM_COMPLETION_LANE_REOPEN_v0: NO" in packet

    for text in (packet, assess):
        assert "does not claim seam closure" in text
        assert "does not claim QFT-GR unification completeness" in text

    assert "does not authorize packet42 hold release" in packet
    assert "does not lift Packet42 hold" in assess


def test_sliceb_increment15_status_tokens_present() -> None:
    packet = _read(INCREMENT15_PACKET_PATH)
    assess = _read(INCREMENT15_ASSESS_PATH)

    assert "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT15_STATUS_v0: EXECUTED_BOUNDED_v0" in packet
    assert "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT15_ASSESSMENT_STATUS_v0: ASSESSED_BOUNDED_v0" in assess
    assert "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT15_OBJECTIVE_ADVANCEMENT_v0: YES" in assess
    assert "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT15_WITNESS_STRENGTHENING_MONOTONICITY_DEPENDENCY_v0: ENFORCED" in assess


def test_sliceb_increment15_packet_assessment_semantic_delta_alignment() -> None:
    packet = _read(INCREMENT15_PACKET_PATH)
    assess = _read(INCREMENT15_ASSESS_PATH)

    # Increment15 must stay aligned on what was newly added and why it matters.
    assert "witness-strengthening monotonicity dependency" in packet
    assert "witness-strengthening monotonicity dependency" in assess
    assert "controlled admissibility-input augmentation" in packet
    assert "controlled same-epoch admissibility-input strengthening" in assess
    assert "degraded or context-divergent admissible outcomes" in packet
    assert "degraded or context-divergent admissible outcomes" in assess


def test_sliceb_increment15_forbidden_overclaim_and_drift_phrases_absent() -> None:
    packet = _read(INCREMENT15_PACKET_PATH)
    assess = _read(INCREMENT15_ASSESS_PATH)

    forbidden_phrases = [
        "seam closure achieved",
        "claims qft-gr unification completeness",
        "authorizes packet42 hold release",
        "lifts Packet42 hold",
    ]

    for text in (packet, assess):
        lowered = text.lower()
        for phrase in forbidden_phrases:
            assert phrase.lower() not in lowered
