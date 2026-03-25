from __future__ import annotations

from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
INCREMENT29_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT29_EXECUTION_PACKET_v0.md"
)
INCREMENT29_ASSESS_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT29_ASSESSMENT_NOTE_v0.md"
)
DECISION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT29_SEMANTIC_DELTA_DECISION_NOTE_v0.md"
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


def test_sliceb_increment29_artifacts_exist() -> None:
    for p in (INCREMENT29_PACKET_PATH, INCREMENT29_ASSESS_PATH):
        assert p.exists(), f"Missing Slice B Increment29 artifact: {p}"


def test_sliceb_increment29_anchor_and_delta_parity() -> None:
    objective = _read(OBJECTIVE_PATH)
    parent = _read(PARENT_PACKET_PATH)
    decision = _read(DECISION_PATH)
    packet = _read(INCREMENT29_PACKET_PATH)
    assess = _read(INCREMENT29_ASSESS_PATH)

    assert REQUIRED_QUESTION in objective
    assert REQUIRED_QUESTION in parent
    assert REQUIRED_QUESTION in decision

    for text in (packet, assess):
        assert "formal/docs/paper/TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_v0.md" in text
        assert "formal/docs/release/QFT_GR_SEAM_REACTIVATION_SLICEB_BOUNDED_EXECUTION_PACKET_v0.md" in text
        assert REQUIRED_QUESTION in text

    assert "formal/docs/release/QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT29_SEMANTIC_DELTA_DECISION_NOTE_v0.md" in packet
    assert "fixed final admissibility input union" in packet
    assert "admissible minimal normal-form completion routes" in packet
    assert "completion-trace invariance" in packet


def test_sliceb_increment29_invariance_and_nonclaim_markers() -> None:
    packet = _read(INCREMENT29_PACKET_PATH)
    assess = _read(INCREMENT29_ASSESS_PATH)

    assert REQUIRED_HOLD_TOKEN in packet
    assert "SCALAR_FREEZE_INVARIANCE_v0: ENFORCED" in packet
    assert "WORKFLOW_CLOSURE_INVARIANCE_v0: ENFORCED" in packet
    assert "GR_QM_COMPLETION_LANE_REOPEN_v0: NO" in packet

    for text in (packet, assess):
        assert "does not claim seam closure" in text
        assert "does not claim QFT-GR unification completeness" in text

    assert "does not authorize packet42 hold release" in packet
    assert "does not lift Packet42 hold" in assess


def test_sliceb_increment29_status_tokens_present() -> None:
    packet = _read(INCREMENT29_PACKET_PATH)
    assess = _read(INCREMENT29_ASSESS_PATH)

    assert "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT29_STATUS_v0: EXECUTED_BOUNDED_v0" in packet
    assert "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT29_ASSESSMENT_STATUS_v0: ASSESSED_BOUNDED_v0" in assess
    assert "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT29_OBJECTIVE_ADVANCEMENT_v0: YES" in assess
    assert (
        "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT29_COMPLETION_TRACE_INVARIANCE_DEPENDENCY_OVER_ADMISSIBLE_MINIMAL_NORMAL_FORM_COMPLETION_ROUTES_v0: ENFORCED"
    ) in assess


def test_sliceb_increment29_packet_assessment_semantic_delta_alignment() -> None:
    packet = _read(INCREMENT29_PACKET_PATH)
    assess = _read(INCREMENT29_ASSESS_PATH)

    assert "completion-trace invariance dependency" in packet
    assert "completion-trace invariance dependency" in assess
    assert "fixed final admissibility input union" in packet
    assert "fixed final admissibility input union" in assess
    assert "admissible minimal normal-form completion alternatives" in packet
    assert "admissible minimal normal-form completion alternatives" in assess


def test_sliceb_increment29_forbidden_overclaim_and_drift_phrases_absent() -> None:
    packet = _read(INCREMENT29_PACKET_PATH)
    assess = _read(INCREMENT29_ASSESS_PATH)

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
