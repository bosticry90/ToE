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
QFT_EVOL_MICRO01_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_EVOL_MICRO_01_TIME_STATE_OPERATOR_SURFACE_v0.md"
)
QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "QFT" / "Evolution" / "ObjectScaffold.lean"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qft_evol_micro01_artifacts_exist() -> None:
    assert QFT_EVOL_TARGET_PATH.exists(), "Missing QFT evolution target document."
    assert QFT_EVOL_MICRO01_PATH.exists(), "Missing QFT evolution Cycle-001 micro document."
    assert QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH.exists(), "Missing QFT evolution object scaffold Lean module."


def test_qft_evol_target_references_micro01_and_gate() -> None:
    text = _read(QFT_EVOL_TARGET_PATH)
    required_tokens = [
        "TARGET-QFT-EVOL-MICRO-01-TIME-STATE-OPERATOR-SURFACE-v0",
        "formal/docs/paper/DERIVATION_TARGET_QFT_EVOL_MICRO_01_TIME_STATE_OPERATOR_SURFACE_v0.md",
        "formal/python/tests/test_qft_evol_micro01_time_state_operator_surface_gate.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT evolution target document is missing required micro-01 token(s): " + ", ".join(missing)


def test_qft_evol_micro01_contains_time_state_operator_boundary_and_lean_pointer_tokens() -> None:
    text = _read(QFT_EVOL_MICRO01_PATH)
    required_tokens = [
        "DERIVATION_TARGET_QFT_EVOL_MICRO_01_TIME_STATE_OPERATOR_SURFACE_v0",
        "TARGET-QFT-EVOL-MICRO-01-TIME-STATE-OPERATOR-SURFACE-v0",
        "QFT_EVOL_MICRO01_TIME_STATE_OPERATOR_ADJUDICATION: NOT_YET_DISCHARGED",
        "QFT_EVOL_MICRO01_SCOPE_BOUNDARY_v0: TIME_STATE_OPERATOR_SURFACE_ONLY_NONCLAIM",
        "QFT_EVOL_MICRO01_PROGRESS_v0: TIME_STATE_OPERATOR_SURFACE_TOKEN_PINNED",
        "QFT_EVOL_MICRO01_TIME_SURFACE_v0: TIME_PARAMETER_TYPED_OBJECT_PINNED",
        "QFT_EVOL_MICRO01_STATE_SURFACE_v0: FIELD_STATE_TYPED_OBJECT_PINNED",
        "QFT_EVOL_MICRO01_OPERATOR_SURFACE_v0: EVOLUTION_OPERATOR_TYPED_OBJECT_PINNED",
        "formal/toe_formal/ToeFormal/QFT/Evolution/ObjectScaffold.lean",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT evolution micro-01 document is missing required token(s): " + ", ".join(missing)


def test_qft_evol_micro01_nonclaim_boundary_is_explicit() -> None:
    text = _read(QFT_EVOL_MICRO01_PATH)
    required_nonclaim_phrases = [
        "time/state/operator scaffold scope only.",
        "statement-only typed objects (no dynamics equation, no closure).",
        "no quantization claim.",
        "no dynamics derivation claim.",
        "no Standard Model recovery claim.",
        "no external truth claim.",
    ]
    missing = [phrase for phrase in required_nonclaim_phrases if phrase not in text]
    assert not missing, "QFT evolution micro-01 non-claim boundary phrase(s) missing: " + ", ".join(missing)


def test_qft_evol_micro01_lean_scaffold_has_time_state_operator_tokens() -> None:
    text = _read(QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "structure TimeParameterObject",
        "structure FieldStateObject",
        "structure EvolutionOperatorObject",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT evolution object scaffold Lean module missing micro-01 token(s): " + ", ".join(missing)
