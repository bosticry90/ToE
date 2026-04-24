from __future__ import annotations

from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
QFT_GAUGE_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_GAUGE_OBJECT_v0.md"
QFT_GAUGE_MICRO02_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_GAUGE_MICRO_02_CONNECTION_SURFACE_v0.md"
)
QFT_GAUGE_OBJECT_SCAFFOLD_LEAN_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "QFT" / "Gauge" / "ObjectScaffold.lean"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qft_gauge_micro02_artifacts_exist() -> None:
    assert QFT_GAUGE_TARGET_PATH.exists(), "Missing QFT gauge target document."
    assert QFT_GAUGE_MICRO02_PATH.exists(), "Missing QFT gauge Cycle-002 micro document."
    assert QFT_GAUGE_OBJECT_SCAFFOLD_LEAN_PATH.exists(), "Missing QFT gauge object scaffold Lean module."


def test_qft_gauge_target_references_micro02_and_gate() -> None:
    text = _read(QFT_GAUGE_TARGET_PATH)
    required_tokens = [
        "TARGET-QFT-GAUGE-MICRO-02-CONNECTION-SURFACE-v0",
        "formal/docs/paper/DERIVATION_TARGET_QFT_GAUGE_MICRO_02_CONNECTION_SURFACE_v0.md",
        "formal/python/tests/test_qft_gauge_micro02_connection_surface_gate.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT gauge target document is missing required micro-02 token(s): " + ", ".join(missing)


def test_qft_gauge_micro02_contains_connection_boundary_and_lean_pointer_tokens() -> None:
    text = _read(QFT_GAUGE_MICRO02_PATH)
    required_tokens = [
        "DERIVATION_TARGET_QFT_GAUGE_MICRO_02_CONNECTION_SURFACE_v0",
        "TARGET-QFT-GAUGE-MICRO-02-CONNECTION-SURFACE-v0",
        "QFT_GAUGE_MICRO02_CONNECTION_ADJUDICATION: NOT_YET_DISCHARGED",
        "QFT_GAUGE_MICRO02_SCOPE_BOUNDARY_v0: CONNECTION_SURFACE_ONLY_NONCLAIM",
        "QFT_GAUGE_MICRO02_PROGRESS_v0: CONNECTION_SURFACE_TOKEN_PINNED",
        "QFT_GAUGE_MICRO02_CONNECTION_SURFACE_v0: A_OBJECT_SURFACE_PINNED",
        "formal/toe_formal/ToeFormal/QFT/Gauge/ObjectScaffold.lean",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT gauge micro-02 document is missing required token(s): " + ", ".join(missing)


def test_qft_gauge_micro02_nonclaim_boundary_is_explicit() -> None:
    text = _read(QFT_GAUGE_MICRO02_PATH)
    required_nonclaim_phrases = [
        "connection scaffold scope only.",
        "no curvature closure claim.",
        "no dynamics derivation claim.",
        "no quantization claim.",
        "no Standard Model recovery claim.",
        "no external truth claim.",
    ]
    missing = [phrase for phrase in required_nonclaim_phrases if phrase not in text]
    assert not missing, "QFT gauge micro-02 non-claim boundary phrase(s) missing: " + ", ".join(missing)
