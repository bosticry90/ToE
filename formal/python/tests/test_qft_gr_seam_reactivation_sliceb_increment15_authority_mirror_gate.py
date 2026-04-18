from __future__ import annotations

from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
DECISION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT15_SEMANTIC_DELTA_DECISION_NOTE_v0.md"
)
PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT15_EXECUTION_PACKET_v0.md"
)
ASSESS_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT15_ASSESSMENT_NOTE_v0.md"
)
SYNTHESIS_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT01_TO_15_SYNTHESIS_NOTE_v0.md"
)

REQUIRED_QUESTION = "stress_energy_to_weak_curvature_handoff_strengthening"
REQUIRED_HOLD_TOKEN = "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_increment15_bundle_local_statuses_and_hold_invariance() -> None:
    decision = _read(DECISION_PATH)
    packet = _read(PACKET_PATH)
    assess = _read(ASSESS_PATH)
    synthesis = _read(SYNTHESIS_PATH)

    for text in (decision, packet, synthesis):
        assert REQUIRED_QUESTION in text
        assert REQUIRED_HOLD_TOKEN in text
        assert "does not claim seam closure" in text
        assert "does not claim QFT-GR unification completeness" in text

    assert REQUIRED_QUESTION in assess
    assert "Packet42 hold remained unchanged." in assess
    assert "does not claim seam closure" in assess
    assert "does not claim QFT-GR unification completeness" in assess

    assert (
        "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT15_SEMANTIC_DELTA_STATUS_v0: "
        "DEFINED_ADDITIVE_DELTA_READY_FOR_BOUNDED_INCREMENT"
    ) in decision
    assert (
        "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT15_OPEN_CONDITION_v0: "
        "SATISFIED_BY_EXPLICIT_WITNESS_STRENGTHENING_MONOTONICITY_DEPENDENCY_CRITERION"
    ) in decision
    assert "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT15_STATUS_v0: EXECUTED_BOUNDED_v0" in packet
    assert "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT15_ASSESSMENT_STATUS_v0: ASSESSED_BOUNDED_v0" in assess
    assert (
        "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT01_TO_15_SYNTHESIS_STATUS_v0: "
        "SYNTHESIZED_BOUNDED_v0"
    ) in synthesis


def test_increment15_bundle_is_mirrored_in_authority_surfaces() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    required_refs = [
        "formal/docs/release/QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT15_SEMANTIC_DELTA_DECISION_NOTE_v0.md",
        "formal/docs/release/QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT15_EXECUTION_PACKET_v0.md",
        "formal/docs/release/QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT15_ASSESSMENT_NOTE_v0.md",
        "formal/docs/release/QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT01_TO_15_SYNTHESIS_NOTE_v0.md",
        "formal/python/tests/test_qft_gr_seam_reactivation_sliceb_increment15_authority_mirror_gate.py",
    ]
    for ref in required_refs:
        assert ref in state_text or ref in inventory_text, f"Missing Increment15 authority ref in state/inventory: {ref}"
        assert ref in roadmap_text, f"Missing Increment15 authority ref in roadmap: {ref}"

    required_tokens = [
        "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT15_SEMANTIC_DELTA_STATUS_v0: DEFINED_ADDITIVE_DELTA_READY_FOR_BOUNDED_INCREMENT",
        "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT15_OPEN_CONDITION_v0: SATISFIED_BY_EXPLICIT_WITNESS_STRENGTHENING_MONOTONICITY_DEPENDENCY_CRITERION",
        "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT15_STATUS_v0: EXECUTED_BOUNDED_v0",
        "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT15_ASSESSMENT_STATUS_v0: ASSESSED_BOUNDED_v0",
        "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT01_TO_15_SYNTHESIS_STATUS_v0: SYNTHESIZED_BOUNDED_v0",
    ]
    for token in required_tokens:
        assert token in state_text or token in inventory_text, f"Missing Increment15 authority token in state/inventory: {token}"
        assert token in roadmap_text, f"Missing Increment15 authority token in roadmap: {token}"
