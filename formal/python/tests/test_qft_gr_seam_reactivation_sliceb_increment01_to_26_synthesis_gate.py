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
SYNTHESIS_0126_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT01_TO_26_SYNTHESIS_NOTE_v0.md"
)
SYNTHESIS_0125_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT01_TO_25_SYNTHESIS_NOTE_v0.md"
)
INCREMENT26_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT26_EXECUTION_PACKET_v0.md"
)
OBJECTIVE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_v0.md"

REQUIRED_QUESTION = "stress_energy_to_weak_curvature_handoff_strengthening"
REQUIRED_HOLD_TOKEN = "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_synthesis_0126_exists_and_is_anchored() -> None:
    synthesis = _read(SYNTHESIS_0126_PATH)
    synthesis_0125 = _read(SYNTHESIS_0125_PATH)
    objective = _read(OBJECTIVE_PATH)
    increment26 = _read(INCREMENT26_PACKET_PATH)

    assert REQUIRED_QUESTION in objective
    assert REQUIRED_QUESTION in synthesis_0125
    assert REQUIRED_QUESTION in increment26
    assert REQUIRED_QUESTION in synthesis
    assert "formal/docs/paper/TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_v0.md" in synthesis
    assert "formal/docs/release/QFT_GR_SEAM_REACTIVATION_SLICEB_BOUNDED_EXECUTION_PACKET_v0.md" in synthesis
    assert "formal/docs/release/QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT01_TO_25_SYNTHESIS_NOTE_v0.md" in synthesis


def test_synthesis_0126_contains_required_sections() -> None:
    synthesis = _read(SYNTHESIS_0126_PATH)

    required_sections = [
        "## 1) Cumulative Establishment (Increment01-26)",
        "## 2) Interaction: Confluence Coherence with Prior Constraint Stack",
        "## 3) Open Items (Still Unresolved)",
        "## 4) Increment27 Decision Question",
        "## 5) Packet42 Hold Rationale",
        "## 6) Non-Claim Boundary",
    ]
    for section in required_sections:
        assert section in synthesis


def test_synthesis_0126_tokens_present() -> None:
    synthesis = _read(SYNTHESIS_0126_PATH)

    assert REQUIRED_HOLD_TOKEN in synthesis
    assert (
        "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT27_DECISION_RULE_v0: "
        "REQUIRE_NEW_INCOMPATIBILITY_OR_DEPENDENCY_CRITERION_BEYOND_ORIGIN_PROVENANCE_EPOCH_BRANCH_IRREVERSIBILITY_FALLBACK_COMPLETENESS_WITNESS_CONSISTENCY_MINIMALITY_UNIQUENESS_REEVALUATION_STABILITY_STRENGTHENING_MONOTONICITY_STRENGTHENING_ORDER_INVARIANCE_STRENGTHENING_PARTITION_INVARIANCE_STRENGTHENING_REPLAY_IDEMPOTENCE_REPLAY_CONVERGENCE_STOP_TERMINATION_CERTIFICATE_DETERMINACY_TERMINATION_CERTIFICATE_STABILITY_REFINEMENT_COMPOSITIONAL_CLOSURE_ASSOCIATIVITY_COHERENCE_IDENTITY_COHERENCE_NEUTRAL_REPRESENTATIVE_CONGRUENCE_CONFLUENCE_COHERENCE_STACK"
    ) in synthesis
    assert (
        "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT01_TO_26_SYNTHESIS_STATUS_v0: "
        "SYNTHESIZED_BOUNDED_v0"
    ) in synthesis


def test_synthesis_0126_nonclaim_markers_present() -> None:
    synthesis = _read(SYNTHESIS_0126_PATH)

    assert "does not claim seam closure" in synthesis
    assert "does not claim QFT-GR unification completeness" in synthesis
    assert "does not authorize packet42 hold release" in synthesis
    assert "does not reopen scalar/workflow/GR-QM lines" in synthesis
