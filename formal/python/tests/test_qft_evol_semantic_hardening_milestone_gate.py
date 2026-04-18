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

MILESTONE_TOKEN = (
    "QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_v0: "
    "CANONICAL_MOMENTUM_HAMILTONIAN_UNITARITY_CHAIN_PINNED"
)
CYCLE2_PROGRESS_TOKEN = "QFT_FULL_DERIVATION_PROGRESS_CYCLE2_v0: SEMANTIC_HARDENING_MILESTONE_TOKEN_PINNED"
MILESTONE_GATE_PATH = "formal/python/tests/test_qft_evol_semantic_hardening_milestone_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qft_evol_semantic_hardening_milestone_artifacts_exist() -> None:
    assert QFT_EVOL_TARGET_PATH.exists(), "Missing QFT evolution umbrella target document."
    assert QFT_FULL_DISCHARGE_TARGET_PATH.exists(), "Missing QFT full-derivation discharge target document."
    assert QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH.exists(), "Missing QFT evolution object scaffold Lean module."
    assert ROADMAP_PATH.exists(), "Missing PHYSICS roadmap document."
    assert STATE_PATH.exists(), "Missing state checkpoint document."


def test_qft_semantic_hardening_milestone_tokens_are_pinned_in_qft_docs() -> None:
    evol_text = _read(QFT_EVOL_TARGET_PATH)
    discharge_text = _read(QFT_FULL_DISCHARGE_TARGET_PATH)

    assert MILESTONE_TOKEN in evol_text, "QFT evolution umbrella target missing semantic-hardening milestone token."
    assert MILESTONE_TOKEN in discharge_text, "QFT full-derivation discharge target missing semantic-hardening milestone token."
    assert CYCLE2_PROGRESS_TOKEN in discharge_text, "QFT full-derivation discharge target missing cycle-2 progress token."


def test_qft_semantic_hardening_milestone_gate_is_pinned_in_authority_surfaces() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)

    assert MILESTONE_GATE_PATH in roadmap_text, (
        f"Roadmap authority surface must pin `{MILESTONE_GATE_PATH}`."
    )
    assert MILESTONE_GATE_PATH in state_text or MILESTONE_GATE_PATH in inventory_text, (
        f"State/Inventory authority surface must pin `{MILESTONE_GATE_PATH}`."
    )
    assert MILESTONE_TOKEN in state_text or MILESTONE_TOKEN in inventory_text, (
        "State/Inventory authority surface missing semantic-hardening milestone token."
    )
    assert CYCLE2_PROGRESS_TOKEN in state_text or CYCLE2_PROGRESS_TOKEN in inventory_text, (
        "State/Inventory authority surface missing cycle-2 progress token."
    )


def test_qft_evol_object_scaffold_contains_required_hardening_theorem_tokens() -> None:
    text = _read(QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "def CanonicalMomentumSurface",
        "theorem qft_evol_canonical_momentum_surface_hardened_v0",
        "theorem qft_evol_hamiltonian_generator_compatibility_hardened_v0",
        "theorem qft_evol_unitarity_injective_step_surface_hardened_v0",
        "theorem qft_evol_generator_unitarity_chain_v0",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT evolution Lean scaffold missing semantic-hardening token(s): " + ", ".join(missing)


def test_qft_targeted_seams_are_not_true_placeholders() -> None:
    text = _read(QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH)

    h_def_start = text.find("def HamiltonianGeneratorInterfaceStatementOnly")
    h_def_end = text.find("theorem HamiltonianGeneratorInterfaceStatementOnly_holds", h_def_start)
    assert h_def_start >= 0 and h_def_end > h_def_start, (
        "Could not isolate Hamiltonian-generator interface definition block."
    )
    h_def_block = text[h_def_start:h_def_end]
    assert "True" not in h_def_block, (
        "Hamiltonian-generator interface seam must not remain a `True` placeholder."
    )
    assert "∀ state : State, generator.step state = hamiltonian.step state" in h_def_block, (
        "Hamiltonian-generator interface seam must use explicit compatibility equality."
    )

    u_def_start = text.find("def UnitarityStatementOnly")
    u_def_end = text.find("theorem UnitarityStatementOnly_holds", u_def_start)
    assert u_def_start >= 0 and u_def_end > u_def_start, (
        "Could not isolate unitarity definition block."
    )
    u_def_block = text[u_def_start:u_def_end]
    assert "True" not in u_def_block, "Unitarity seam must not remain a `True` placeholder."
    assert "Function.Injective step" in u_def_block, (
        "Unitarity hardening seam must use an explicit injectivity surface."
    )

    assert "canonicalMomentum.map field = momentum" in text, (
        "Canonical momentum hardening seam must use an explicit mapping equality surface."
    )


def test_qft_generator_unitarity_chain_is_nontrivial() -> None:
    text = _read(QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH)
    anchor = "theorem qft_evol_generator_unitarity_chain_v0"
    idx = text.find(anchor)
    assert idx >= 0, "Missing generator-unitarity chain theorem token."

    snippet = text[idx : idx + 1200]
    assert "trivial" not in snippet, (
        "Generator-unitarity chain theorem must not be implemented as a trivial placeholder proof."
    )
