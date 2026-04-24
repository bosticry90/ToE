from __future__ import annotations

from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
QFT_EVOL_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0.md"
QFT_EVOL_MICRO03_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_EVOL_MICRO_03_ACTION_DENSITY_SURFACE_v0.md"
)
QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "QFT" / "Evolution" / "ObjectScaffold.lean"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qft_evol_micro03_artifacts_exist() -> None:
    assert QFT_EVOL_TARGET_PATH.exists(), "Missing QFT evolution target document."
    assert QFT_EVOL_MICRO03_PATH.exists(), "Missing QFT evolution Cycle-003 micro document."
    assert QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH.exists(), "Missing QFT evolution object scaffold Lean module."


def test_qft_evol_target_references_micro03_and_gate() -> None:
    text = _read(QFT_EVOL_TARGET_PATH)
    required_tokens = [
        "TARGET-QFT-EVOL-MICRO-03-ACTION-DENSITY-SURFACE-v0",
        "formal/docs/paper/DERIVATION_TARGET_QFT_EVOL_MICRO_03_ACTION_DENSITY_SURFACE_v0.md",
        "formal/python/tests/test_qft_evol_micro03_action_density_surface_gate.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT evolution target document is missing required micro-03 token(s): " + ", ".join(missing)


def test_qft_evol_micro03_contains_action_density_boundary_and_lean_pointer_tokens() -> None:
    text = _read(QFT_EVOL_MICRO03_PATH)
    required_tokens = [
        "DERIVATION_TARGET_QFT_EVOL_MICRO_03_ACTION_DENSITY_SURFACE_v0",
        "TARGET-QFT-EVOL-MICRO-03-ACTION-DENSITY-SURFACE-v0",
        "QFT_EVOL_MICRO03_ACTION_DENSITY_ADJUDICATION: NOT_YET_DISCHARGED",
        "QFT_EVOL_MICRO03_SCOPE_BOUNDARY_v0: ACTION_DENSITY_SURFACE_ONLY_NONCLAIM",
        "QFT_EVOL_MICRO03_PROGRESS_v0: ACTION_DENSITY_SURFACE_TOKEN_PINNED",
        "QFT_EVOL_MICRO03_ACTION_DENSITY_SURFACE_v0: ACTION_DENSITY_TYPED_OBJECT_PINNED",
        "formal/toe_formal/ToeFormal/QFT/Evolution/ObjectScaffold.lean",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT evolution micro-03 document is missing required token(s): " + ", ".join(missing)


def test_qft_evol_micro03_nonclaim_boundary_is_explicit() -> None:
    text = _read(QFT_EVOL_MICRO03_PATH)
    required_nonclaim_phrases = [
        "action-density scaffold scope only.",
        "statement-only placeholder (no closure).",
        "no quantization claim.",
        "no dynamics derivation claim.",
        "no Standard Model recovery claim.",
        "no external truth claim.",
    ]
    missing = [phrase for phrase in required_nonclaim_phrases if phrase not in text]
    assert not missing, "QFT evolution micro-03 non-claim boundary phrase(s) missing: " + ", ".join(missing)


def test_qft_evol_micro03_lean_scaffold_has_action_density_token() -> None:
    text = _read(QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "structure ActionDensity",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT evolution object scaffold Lean module missing micro-03 token(s): " + ", ".join(missing)
