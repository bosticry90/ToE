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
QFT_EVOL_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0.md"
QFT_FULL_DISCHARGE_TARGET_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md"
)
QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "QFT" / "Evolution" / "ObjectScaffold.lean"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"

CYCLE15_PROGRESS_TOKEN = (
    "QFT_FULL_DERIVATION_PROGRESS_CYCLE15_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_SYMMETRY_WITNESS_NORMALIZATION_TOKEN_PINNED"
)
CYCLE15_MILESTONE_TOKEN = (
    "QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE15_v0: GENERATOR_UNITARITY_ROUTE_ALIGNMENT_SYMMETRY_WITNESS_COHERENCE_SYMMETRY_WITNESS_NORMALIZATION_PINNED"
)
CYCLE15_GATE_PATH = "formal/python/tests/test_qft_evol_semantic_hardening_cycle15_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _snippet(text: str, start_token: str, end_token: str) -> str:
    start = text.find(start_token)
    assert start >= 0, f"Missing anchor token `{start_token}`."
    end = text.find(end_token, start)
    assert end > start, f"Missing end anchor token `{end_token}` after `{start_token}`."
    return text[start:end]


def test_qft_cycle15_hardening_artifacts_exist() -> None:
    assert QFT_EVOL_TARGET_PATH.exists(), "Missing QFT evolution umbrella target document."
    assert QFT_FULL_DISCHARGE_TARGET_PATH.exists(), "Missing QFT full-derivation discharge target document."
    assert QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH.exists(), "Missing QFT evolution object scaffold Lean module."
    assert ROADMAP_PATH.exists(), "Missing PHYSICS roadmap document."
    assert STATE_PATH.exists(), "Missing state checkpoint document."


def test_qft_cycle15_tokens_are_pinned_in_qft_docs() -> None:
    evol_text = _read(QFT_EVOL_TARGET_PATH)
    discharge_text = _read(QFT_FULL_DISCHARGE_TARGET_PATH)

    for token in [CYCLE15_MILESTONE_TOKEN, CYCLE15_GATE_PATH]:
        assert token in evol_text, f"QFT evolution umbrella target missing cycle-15 token `{token}`."
        assert token in discharge_text, f"QFT full-derivation discharge target missing cycle-15 token `{token}`."

    assert CYCLE15_PROGRESS_TOKEN in discharge_text, "QFT full-derivation discharge target missing cycle-15 progress token."


def test_qft_cycle15_gate_is_pinned_in_authority_surfaces() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)

    assert CYCLE15_GATE_PATH in roadmap_text, f"Roadmap authority surface must pin `{CYCLE15_GATE_PATH}`."
    assert CYCLE15_GATE_PATH in state_text or CYCLE15_GATE_PATH in inventory_text, (
        f"State/Inventory authority surface must pin `{CYCLE15_GATE_PATH}`."
    )
    assert CYCLE15_MILESTONE_TOKEN in state_text or CYCLE15_MILESTONE_TOKEN in inventory_text, (
        "State/Inventory authority surface missing cycle-15 milestone token."
    )
    assert CYCLE15_PROGRESS_TOKEN in state_text or CYCLE15_PROGRESS_TOKEN in inventory_text, (
        "State/Inventory authority surface missing cycle-15 progress token."
    )


def test_qft_cycle15_alignment_symmetry_witness_coherence_symmetry_witness_normalization_theorem_token_is_present() -> None:
    text = _read(QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH)
    assert (
        "theorem qft_evol_generator_unitarity_route_alignment_symmetry_witness_coherence_symmetry_witness_normalization_v0"
        in text
    ), "QFT evolution Lean scaffold missing cycle-15 alignment-symmetry witness coherence-symmetry-witness normalization theorem token."


def test_qft_cycle15_alignment_symmetry_witness_coherence_symmetry_witness_normalization_reuses_cycle14_via_symmetry() -> None:
    text = _read(QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH)
    theorem_block = _snippet(
        text,
        "theorem qft_evol_generator_unitarity_route_alignment_symmetry_witness_coherence_symmetry_witness_normalization_v0",
        "end",
    )

    for token in [
        "qft_evol_generator_unitarity_route_alignment_symmetry_witness_coherence_alignment_v0",
        "qft_evol_generator_unitarity_route_alignment_symmetry_witness_coherence_normalization_v0",
        "qft_evol_generator_unitarity_route_alignment_symmetry_witness_coherence_symmetry_witness_v0",
        "hReflectsState : Function.Injective canonicalMomentum.map",
        "hCompat : HamiltonianGeneratorInterfaceStatementOnly hamiltonian generator",
        "hHamiltonianInvariant : CanonicalMomentumInvariantUnderStep canonicalMomentum hamiltonian.step",
        ").symm",
    ]:
        assert token in theorem_block, f"Cycle-15 theorem missing expected token `{token}`."

    assert "trivial" not in theorem_block, (
        "Cycle-15 theorem must not be implemented as a trivial placeholder proof."
    )
