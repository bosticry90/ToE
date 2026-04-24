from __future__ import annotations

from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SYNTHESIS_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT01_TO_04_SYNTHESIS_NOTE_v0.md"
)
INCREMENT04_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT04_EXECUTION_PACKET_v0.md"
)
OBJECTIVE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_v0.md"

REQUIRED_QUESTION = "stress_energy_to_weak_curvature_handoff_strengthening"
REQUIRED_HOLD_TOKEN = "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_synthesis_artifact_exists_and_is_anchored() -> None:
    synthesis = _read(SYNTHESIS_PATH)
    objective = _read(OBJECTIVE_PATH)
    increment04 = _read(INCREMENT04_PACKET_PATH)

    assert REQUIRED_QUESTION in objective
    assert REQUIRED_QUESTION in increment04
    assert REQUIRED_QUESTION in synthesis
    assert "formal/docs/paper/TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_v0.md" in synthesis
    assert "formal/docs/release/QFT_GR_SEAM_REACTIVATION_SLICEB_BOUNDED_EXECUTION_PACKET_v0.md" in synthesis


def test_synthesis_contains_required_sections() -> None:
    synthesis = _read(SYNTHESIS_PATH)

    required_sections = [
        "## 1) Cumulative Establishment (Increment01-04)",
        "## 2) Open Items (Still Unresolved)",
        "## 3) Packet42 Hold Rationale",
        "## 4) Decision on Next Move",
        "## 5) Non-Claim Boundary",
    ]
    for section in required_sections:
        assert section in synthesis


def test_synthesis_hold_and_decision_tokens_present() -> None:
    synthesis = _read(SYNTHESIS_PATH)

    assert REQUIRED_HOLD_TOKEN in synthesis
    assert (
        "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT05_DECISION_v0: "
        "CONDITIONAL_PROCEED_ONLY_IF_NEW_SEMANTIC_GAIN"
    ) in synthesis
    assert "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT01_TO_04_SYNTHESIS_STATUS_v0: SYNTHESIZED_BOUNDED_v0" in synthesis


def test_synthesis_nonclaim_markers_present() -> None:
    synthesis = _read(SYNTHESIS_PATH)

    assert "does not claim seam closure" in synthesis
    assert "does not claim QFT-GR unification completeness" in synthesis
    assert "does not authorize packet42 hold release" in synthesis
    assert "does not reopen scalar/workflow/GR-QM lines" in synthesis
