from __future__ import annotations

from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
QFT_EVOL_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0.md"
QFT_EVOL_MICRO06_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_EVOL_MICRO_06_CANONICAL_MOMENTUM_SURFACE_v0.md"
)
QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "QFT" / "Evolution" / "ObjectScaffold.lean"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qft_evol_micro06_artifacts_exist() -> None:
    assert QFT_EVOL_TARGET_PATH.exists(), "Missing QFT evolution target document."
    assert QFT_EVOL_MICRO06_PATH.exists(), "Missing QFT evolution Cycle-006 micro document."
    assert QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH.exists(), "Missing QFT evolution object scaffold Lean module."


def test_qft_evol_target_references_micro06_and_gate() -> None:
    text = _read(QFT_EVOL_TARGET_PATH)
    required_tokens = [
        "TARGET-QFT-EVOL-MICRO-06-CANONICAL-MOMENTUM-SURFACE-v0",
        "formal/docs/paper/DERIVATION_TARGET_QFT_EVOL_MICRO_06_CANONICAL_MOMENTUM_SURFACE_v0.md",
        "formal/python/tests/test_qft_evol_micro06_canonical_momentum_surface_gate.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT evolution target document is missing required micro-06 token(s): " + ", ".join(missing)


def test_qft_evol_micro06_contains_canonical_momentum_boundary_and_lean_pointer_tokens() -> None:
    text = _read(QFT_EVOL_MICRO06_PATH)
    required_tokens = [
        "DERIVATION_TARGET_QFT_EVOL_MICRO_06_CANONICAL_MOMENTUM_SURFACE_v0",
        "TARGET-QFT-EVOL-MICRO-06-CANONICAL-MOMENTUM-SURFACE-v0",
        "QFT_EVOL_MICRO06_CANONICAL_MOMENTUM_ADJUDICATION: NOT_YET_DISCHARGED",
        "QFT_EVOL_MICRO06_SCOPE_BOUNDARY_v0: CANONICAL_MOMENTUM_SURFACE_ONLY_NONCLAIM",
        "QFT_EVOL_MICRO06_PROGRESS_v0: CANONICAL_MOMENTUM_SURFACE_TOKEN_PINNED",
        "QFT_EVOL_MICRO06_CANONICAL_MOMENTUM_SURFACE_v0: CANONICAL_MOMENTUM_STATEMENT_ONLY_PINNED",
        "formal/toe_formal/ToeFormal/QFT/Evolution/ObjectScaffold.lean",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT evolution micro-06 document is missing required token(s): " + ", ".join(missing)


def test_qft_evol_micro06_nonclaim_boundary_is_explicit() -> None:
    text = _read(QFT_EVOL_MICRO06_PATH)
    required_nonclaim_phrases = [
        "canonical momentum statement-only surface (no proof/closure).",
        "no quantization claim.",
        "no dynamics derivation claim.",
        "no Standard Model recovery claim.",
        "no external truth claim.",
    ]
    missing = [phrase for phrase in required_nonclaim_phrases if phrase not in text]
    assert not missing, "QFT evolution micro-06 non-claim boundary phrase(s) missing: " + ", ".join(missing)


def test_qft_evol_micro06_lean_scaffold_has_canonical_momentum_token() -> None:
    text = _read(QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "structure CanonicalMomentum",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT evolution object scaffold Lean module missing micro-06 token(s): " + ", ".join(missing)
