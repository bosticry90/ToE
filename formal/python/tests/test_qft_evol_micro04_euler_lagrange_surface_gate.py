from __future__ import annotations

from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
QFT_EVOL_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0.md"
QFT_EVOL_MICRO04_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_EVOL_MICRO_04_EULER_LAGRANGE_SURFACE_v0.md"
)
QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "QFT" / "Evolution" / "ObjectScaffold.lean"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qft_evol_micro04_artifacts_exist() -> None:
    assert QFT_EVOL_TARGET_PATH.exists(), "Missing QFT evolution target document."
    assert QFT_EVOL_MICRO04_PATH.exists(), "Missing QFT evolution Cycle-004 micro document."
    assert QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH.exists(), "Missing QFT evolution object scaffold Lean module."


def test_qft_evol_target_references_micro04_and_gate() -> None:
    text = _read(QFT_EVOL_TARGET_PATH)
    required_tokens = [
        "TARGET-QFT-EVOL-MICRO-04-EULER-LAGRANGE-SURFACE-v0",
        "formal/docs/paper/DERIVATION_TARGET_QFT_EVOL_MICRO_04_EULER_LAGRANGE_SURFACE_v0.md",
        "formal/python/tests/test_qft_evol_micro04_euler_lagrange_surface_gate.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT evolution target document is missing required micro-04 token(s): " + ", ".join(missing)


def test_qft_evol_micro04_contains_el_boundary_and_lean_pointer_tokens() -> None:
    text = _read(QFT_EVOL_MICRO04_PATH)
    required_tokens = [
        "DERIVATION_TARGET_QFT_EVOL_MICRO_04_EULER_LAGRANGE_SURFACE_v0",
        "TARGET-QFT-EVOL-MICRO-04-EULER-LAGRANGE-SURFACE-v0",
        "QFT_EVOL_MICRO04_EULER_LAGRANGE_ADJUDICATION: NOT_YET_DISCHARGED",
        "QFT_EVOL_MICRO04_SCOPE_BOUNDARY_v0: EULER_LAGRANGE_SURFACE_ONLY_NONCLAIM",
        "QFT_EVOL_MICRO04_PROGRESS_v0: EULER_LAGRANGE_SURFACE_TOKEN_PINNED",
        "QFT_EVOL_MICRO04_EULER_LAGRANGE_SURFACE_v0: EULER_LAGRANGE_STATEMENT_ONLY_PINNED",
        "formal/toe_formal/ToeFormal/QFT/Evolution/ObjectScaffold.lean",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT evolution micro-04 document is missing required token(s): " + ", ".join(missing)


def test_qft_evol_micro04_nonclaim_boundary_is_explicit() -> None:
    text = _read(QFT_EVOL_MICRO04_PATH)
    required_nonclaim_phrases = [
        "Euler-Lagrange statement-only surface (no proof/closure).",
        "no quantization claim.",
        "no dynamics derivation claim.",
        "no Standard Model recovery claim.",
        "no external truth claim.",
    ]
    missing = [phrase for phrase in required_nonclaim_phrases if phrase not in text]
    assert not missing, "QFT evolution micro-04 non-claim boundary phrase(s) missing: " + ", ".join(missing)


def test_qft_evol_micro04_lean_scaffold_has_el_statement_tokens() -> None:
    text = _read(QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "def EulerLagrangeStatementOnly",
        "theorem EulerLagrangeStatementOnly_holds",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT evolution object scaffold Lean module missing micro-04 token(s): " + ", ".join(missing)
