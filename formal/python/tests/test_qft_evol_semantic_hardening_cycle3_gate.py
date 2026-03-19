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

CYCLE3_PROGRESS_TOKEN = "QFT_FULL_DERIVATION_PROGRESS_CYCLE3_v0: CANONICAL_MOMENTUM_INVARIANT_UNITARITY_ROUTE_PINNED"
CYCLE3_MILESTONE_TOKEN = (
    "QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE3_v0: "
    "CANONICAL_MOMENTUM_INVARIANT_UNITARITY_ROUTE_PINNED"
)
CYCLE3_GATE_PATH = "formal/python/tests/test_qft_evol_semantic_hardening_cycle3_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _snippet(text: str, start_token: str, end_token: str, *, extra: int = 0) -> str:
    start = text.find(start_token)
    assert start >= 0, f"Missing anchor token `{start_token}`."
    end = text.find(end_token, start)
    assert end > start, f"Missing end anchor token `{end_token}` after `{start_token}`."
    return text[start : end + extra]


def test_qft_cycle3_hardening_artifacts_exist() -> None:
    assert QFT_EVOL_TARGET_PATH.exists(), "Missing QFT evolution umbrella target document."
    assert QFT_FULL_DISCHARGE_TARGET_PATH.exists(), "Missing QFT full-derivation discharge target document."
    assert QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH.exists(), "Missing QFT evolution object scaffold Lean module."
    assert ROADMAP_PATH.exists(), "Missing PHYSICS roadmap document."
    assert STATE_PATH.exists(), "Missing state checkpoint document."


def test_qft_cycle3_tokens_are_pinned_in_qft_docs() -> None:
    evol_text = _read(QFT_EVOL_TARGET_PATH)
    discharge_text = _read(QFT_FULL_DISCHARGE_TARGET_PATH)

    for token in [CYCLE3_MILESTONE_TOKEN, CYCLE3_GATE_PATH]:
        assert token in evol_text, f"QFT evolution umbrella target missing cycle-3 token `{token}`."
        assert token in discharge_text, f"QFT full-derivation discharge target missing cycle-3 token `{token}`."

    assert CYCLE3_PROGRESS_TOKEN in discharge_text, "QFT full-derivation discharge target missing cycle-3 progress token."


def test_qft_cycle3_gate_is_pinned_in_authority_surfaces() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)

    assert CYCLE3_GATE_PATH in roadmap_text, f"Roadmap authority surface must pin `{CYCLE3_GATE_PATH}`."
    assert CYCLE3_GATE_PATH in state_text or CYCLE3_GATE_PATH in inventory_text, (
        f"State/Inventory authority surface must pin `{CYCLE3_GATE_PATH}`."
    )
    assert CYCLE3_MILESTONE_TOKEN in state_text or CYCLE3_MILESTONE_TOKEN in inventory_text, (
        "State/Inventory authority surface missing cycle-3 milestone token."
    )
    assert CYCLE3_PROGRESS_TOKEN in state_text or CYCLE3_PROGRESS_TOKEN in inventory_text, (
        "State/Inventory authority surface missing cycle-3 progress token."
    )


def test_qft_cycle3_lean_route_tokens_are_present() -> None:
    text = _read(QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "def CanonicalMomentumInvariantUnderStep",
        "theorem qft_evol_canonical_momentum_invariant_step_surface_hardened_v0",
        "theorem qft_evol_unitarity_of_canonical_momentum_reflective_invariant_step_v0",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT evolution Lean scaffold missing cycle-3 hardening token(s): " + ", ".join(missing)


def test_qft_cycle3_canonical_momentum_invariant_surface_is_explicit_not_placeholder() -> None:
    text = _read(QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH)
    block = _snippet(
        text,
        "def CanonicalMomentumInvariantUnderStep",
        "theorem qft_evol_canonical_momentum_invariant_step_surface_hardened_v0",
    )
    assert "True" not in block, "Canonical-momentum invariant surface must not be a `True` placeholder."
    assert "canonicalMomentum.map (step state) = canonicalMomentum.map state" in block, (
        "Canonical-momentum invariant surface must use explicit momentum-map invariance equality."
    )


def test_qft_cycle3_unitarity_route_theorem_is_nontrivial_and_uses_cycle3_assumptions() -> None:
    text = _read(QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH)
    theorem_block = _snippet(
        text,
        "theorem qft_evol_unitarity_of_canonical_momentum_reflective_invariant_step_v0",
        "end",
    )

    for token in [
        "hReflectsState : Function.Injective canonicalMomentum.map",
        "hInvariant : CanonicalMomentumInvariantUnderStep canonicalMomentum step",
        "apply hReflectsState",
        "rw [hxy]",
    ]:
        assert token in theorem_block, f"Cycle-3 unitarity route theorem missing expected token `{token}`."

    assert "trivial" not in theorem_block, (
        "Cycle-3 unitarity route theorem must not be implemented as a trivial placeholder proof."
    )
