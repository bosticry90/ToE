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
DECISION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT31_SEMANTIC_DELTA_DECISION_NOTE_v0.md"
)
SYNTHESIS_0130_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT01_TO_30_SYNTHESIS_NOTE_v0.md"
)
OBJECTIVE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_v0.md"

REQUIRED_QUESTION = "stress_energy_to_weak_curvature_handoff_strengthening"
REQUIRED_HOLD_TOKEN = "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_increment31_semantic_delta_decision_exists_and_anchors() -> None:
    decision = _read(DECISION_PATH)
    synthesis = _read(SYNTHESIS_0130_PATH)
    objective = _read(OBJECTIVE_PATH)

    assert REQUIRED_QUESTION in objective
    assert REQUIRED_QUESTION in synthesis
    assert REQUIRED_QUESTION in decision
    assert "formal/docs/release/QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT01_TO_30_SYNTHESIS_NOTE_v0.md" in decision
    assert "formal/docs/paper/TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_v0.md" in decision


def test_increment31_semantic_delta_decision_tokens_present() -> None:
    decision = _read(DECISION_PATH)

    assert (
        "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT31_SEMANTIC_DELTA_STATUS_v0: "
        "DEFINED_ADDITIVE_DELTA_READY_FOR_BOUNDED_INCREMENT"
    ) in decision
    assert (
        "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT31_OPEN_CONDITION_v0: "
        "SATISFIED_BY_EXPLICIT_PREFIX_TRANSITION_SIGNATURE_INVARIANCE_DEPENDENCY_CRITERION"
    ) in decision
    assert REQUIRED_HOLD_TOKEN in decision


def test_increment31_semantic_delta_explicit_nonredundancy_basis() -> None:
    decision = _read(DECISION_PATH)

    assert "completion-trace-invariance" in decision
    assert "prefix-invariance" in decision
    assert "prefix-transition-signature invariance" in decision
    assert "canonical transition-signature profile" in decision


def test_increment31_semantic_delta_nonclaim_and_no_auto_open() -> None:
    decision = _read(DECISION_PATH)

    assert "does not claim seam closure" in decision
    assert "does not claim QFT-GR unification completeness" in decision
    assert "does not authorize packet42 hold release" in decision
    assert "does not itself open Increment31" in decision
