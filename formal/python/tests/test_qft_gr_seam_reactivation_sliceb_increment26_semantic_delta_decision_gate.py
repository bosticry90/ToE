from __future__ import annotations

from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
DECISION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT26_SEMANTIC_DELTA_DECISION_NOTE_v0.md"
)
SYNTHESIS_0125_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT01_TO_25_SYNTHESIS_NOTE_v0.md"
)
OBJECTIVE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_v0.md"

REQUIRED_QUESTION = "stress_energy_to_weak_curvature_handoff_strengthening"
REQUIRED_HOLD_TOKEN = "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_increment26_semantic_delta_decision_exists_and_anchors() -> None:
    decision = _read(DECISION_PATH)
    synthesis = _read(SYNTHESIS_0125_PATH)
    objective = _read(OBJECTIVE_PATH)

    assert REQUIRED_QUESTION in objective
    assert REQUIRED_QUESTION in synthesis
    assert REQUIRED_QUESTION in decision
    assert "formal/docs/release/QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT01_TO_25_SYNTHESIS_NOTE_v0.md" in decision
    assert "formal/docs/paper/TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_v0.md" in decision


def test_increment26_semantic_delta_decision_tokens_present() -> None:
    decision = _read(DECISION_PATH)

    assert (
        "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT26_SEMANTIC_DELTA_STATUS_v0: "
        "DEFINED_ADDITIVE_DELTA_READY_FOR_BOUNDED_INCREMENT"
    ) in decision
    assert (
        "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT26_OPEN_CONDITION_v0: "
        "SATISFIED_BY_EXPLICIT_CONFLUENCE_COHERENCE_OF_ADMISSIBLE_NEUTRAL_REPRESENTATIVE_SUBSTITUTION_SEQUENCE_DEPENDENCY_CRITERION"
    ) in decision
    assert REQUIRED_HOLD_TOKEN in decision


def test_increment26_semantic_delta_explicit_nonredundancy_basis() -> None:
    decision = _read(DECISION_PATH)

    assert "ordering refinement" in decision
    assert "admissibility continuity" in decision
    assert "mixed-origin exclusion" in decision
    assert "provenance lock" in decision
    assert "epoch coherence" in decision
    assert "same-epoch branch-irreversibility dependency" in decision
    assert "fallback-activation completeness dependency" in decision
    assert "fallback-precondition witness dependency" in decision
    assert "witness-consistency dependency" in decision
    assert "witness-minimality dependency" in decision
    assert "witness-uniqueness dependency" in decision
    assert "witness-reevaluation stability" in decision
    assert "witness-strengthening monotonicity" in decision
    assert "strengthening-order invariance" in decision
    assert "strengthening-partition invariance" in decision
    assert "strengthening-replay idempotence dependency" in decision
    assert "replay-convergence stop-condition dependency" in decision
    assert "termination-certificate determinacy dependency" in decision
    assert "termination-certificate stability under admissible certificate-preserving refinement dependency" in decision
    assert "compositional closure of admissible certificate-preserving refinement dependency" in decision
    assert "associativity coherence of admissible certificate-preserving refinement composition dependency" in decision
    assert "identity coherence of admissible certificate-preserving refinement composition dependency" in decision
    assert "neutral-representative congruence of admissible certificate-preserving refinement composition dependency" in decision
    assert "confluence coherence" in decision


def test_increment26_semantic_delta_nonclaim_and_no_auto_open() -> None:
    decision = _read(DECISION_PATH)

    assert "does not claim seam closure" in decision
    assert "does not claim QFT-GR unification completeness" in decision
    assert "does not authorize packet42 hold release" in decision
    assert "does not itself open Increment26" in decision
