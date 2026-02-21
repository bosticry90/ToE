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
QFT_EVOL_MICRO17_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_QFT_EVOL_MICRO_17_QFT_EVOLUTION_THEOREM_TOKEN_CONSUMER_BINDING_COMPATIBILITY_SURFACE_v0.md"
)
QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "QFT" / "Evolution" / "ObjectScaffold.lean"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qft_evol_micro17_artifacts_exist() -> None:
    assert QFT_EVOL_TARGET_PATH.exists(), "Missing QFT evolution target document."
    assert QFT_EVOL_MICRO17_PATH.exists(), "Missing QFT evolution Cycle-017 micro document."
    assert QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH.exists(), "Missing QFT evolution object scaffold Lean module."


def test_qft_evol_target_references_micro17_and_gate() -> None:
    text = _read(QFT_EVOL_TARGET_PATH)
    required_tokens = [
        "TARGET-QFT-EVOL-MICRO-17-QFT-EVOLUTION-THEOREM-TOKEN-CONSUMER-BINDING-COMPATIBILITY-SURFACE-v0",
        "formal/docs/paper/DERIVATION_TARGET_QFT_EVOL_MICRO_17_QFT_EVOLUTION_THEOREM_TOKEN_CONSUMER_BINDING_COMPATIBILITY_SURFACE_v0.md",
        "formal/python/tests/test_qft_evol_micro17_qft_evolution_theorem_token_consumer_binding_compatibility_surface_gate.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT evolution target document is missing required micro-17 token(s): " + ", ".join(missing)


def test_qft_evol_micro17_contains_interface_boundary_and_lean_pointer_tokens() -> None:
    text = _read(QFT_EVOL_MICRO17_PATH)
    required_tokens = [
        "DERIVATION_TARGET_QFT_EVOL_MICRO_17_QFT_EVOLUTION_THEOREM_TOKEN_CONSUMER_BINDING_COMPATIBILITY_SURFACE_v0",
        "TARGET-QFT-EVOL-MICRO-17-QFT-EVOLUTION-THEOREM-TOKEN-CONSUMER-BINDING-COMPATIBILITY-SURFACE-v0",
        "QFT_EVOL_MICRO17_QFT_EVOLUTION_THEOREM_TOKEN_CONSUMER_BINDING_COMPATIBILITY_ADJUDICATION: NOT_YET_DISCHARGED",
        "QFT_EVOL_MICRO17_SCOPE_BOUNDARY_v0: QFT_EVOLUTION_THEOREM_TOKEN_CONSUMER_BINDING_COMPATIBILITY_SURFACE_ONLY_NONCLAIM",
        "QFT_EVOL_MICRO17_PROGRESS_v0: QFT_EVOLUTION_THEOREM_TOKEN_CONSUMER_BINDING_COMPATIBILITY_SURFACE_TOKEN_PINNED",
        "QFT_EVOL_MICRO17_QFT_EVOLUTION_THEOREM_TOKEN_CONSUMER_BINDING_COMPATIBILITY_SURFACE_v0: QFT_EVOLUTION_THEOREM_TOKEN_CONSUMER_BINDING_COMPATIBILITY_STATEMENT_ONLY_PINNED",
        "formal/toe_formal/ToeFormal/QFT/Evolution/ObjectScaffold.lean",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT evolution micro-17 document is missing required token(s): " + ", ".join(missing)


def test_qft_evol_micro17_nonclaim_boundary_is_explicit() -> None:
    text = _read(QFT_EVOL_MICRO17_PATH)
    required_nonclaim_phrases = [
        "qft-evolution-theorem-token-consumer-binding-compatibility statement-only surface (no proof/closure).",
        "no quantization claim.",
        "no dynamics derivation claim.",
        "no Standard Model recovery claim.",
        "no external truth claim.",
    ]
    missing = [phrase for phrase in required_nonclaim_phrases if phrase not in text]
    assert not missing, "QFT evolution micro-17 non-claim boundary phrase(s) missing: " + ", ".join(missing)


def test_qft_evol_micro17_lean_scaffold_has_interface_statement_tokens() -> None:
    text = _read(QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "def QFTEvolutionTheoremTokenConsumerBindingCompatibilityStatementOnly",
        "theorem QFTEvolutionTheoremTokenConsumerBindingCompatibilityStatementOnly_holds",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT evolution object scaffold Lean module missing micro-17 token(s): " + ", ".join(missing)
