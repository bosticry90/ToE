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
QFT_GAUGE_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_GAUGE_OBJECT_v0.md"
QFT_GAUGE_MICRO03_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_GAUGE_MICRO_03_CURVATURE_SURFACE_v0.md"
)
QFT_GAUGE_OBJECT_SCAFFOLD_LEAN_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "QFT" / "Gauge" / "ObjectScaffold.lean"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qft_gauge_micro03_artifacts_exist() -> None:
    assert QFT_GAUGE_TARGET_PATH.exists(), "Missing QFT gauge target document."
    assert QFT_GAUGE_MICRO03_PATH.exists(), "Missing QFT gauge Cycle-003 micro document."
    assert QFT_GAUGE_OBJECT_SCAFFOLD_LEAN_PATH.exists(), "Missing QFT gauge object scaffold Lean module."


def test_qft_gauge_target_references_micro03_and_gate() -> None:
    text = _read(QFT_GAUGE_TARGET_PATH)
    required_tokens = [
        "TARGET-QFT-GAUGE-MICRO-03-CURVATURE-SURFACE-v0",
        "formal/docs/paper/DERIVATION_TARGET_QFT_GAUGE_MICRO_03_CURVATURE_SURFACE_v0.md",
        "formal/python/tests/test_qft_gauge_micro03_curvature_surface_gate.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT gauge target document is missing required micro-03 token(s): " + ", ".join(missing)


def test_qft_gauge_micro03_contains_curvature_boundary_and_lean_pointer_tokens() -> None:
    text = _read(QFT_GAUGE_MICRO03_PATH)
    required_tokens = [
        "DERIVATION_TARGET_QFT_GAUGE_MICRO_03_CURVATURE_SURFACE_v0",
        "TARGET-QFT-GAUGE-MICRO-03-CURVATURE-SURFACE-v0",
        "QFT_GAUGE_MICRO03_CURVATURE_ADJUDICATION: NOT_YET_DISCHARGED",
        "QFT_GAUGE_MICRO03_SCOPE_BOUNDARY_v0: CURVATURE_SURFACE_ONLY_NONCLAIM",
        "QFT_GAUGE_MICRO03_PROGRESS_v0: CURVATURE_SURFACE_TOKEN_PINNED",
        "QFT_GAUGE_MICRO03_CURVATURE_SURFACE_v0: F_OBJECT_SURFACE_PINNED",
        "QFT_GAUGE_MICRO03_CURVATURE_RELATION_SURFACE_v0: F_EQ_DA_PLUS_A_WEDGE_A_PLACEHOLDER_DECLARED",
        "formal/toe_formal/ToeFormal/QFT/Gauge/ObjectScaffold.lean",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT gauge micro-03 document is missing required token(s): " + ", ".join(missing)


def test_qft_gauge_micro03_nonclaim_boundary_is_explicit() -> None:
    text = _read(QFT_GAUGE_MICRO03_PATH)
    required_nonclaim_phrases = [
        "curvature scaffold scope only.",
        "placeholder relation only (no proof/closure).",
        "no dynamics derivation claim.",
        "no quantization claim.",
        "no Standard Model recovery claim.",
        "no external truth claim.",
    ]
    missing = [phrase for phrase in required_nonclaim_phrases if phrase not in text]
    assert not missing, "QFT gauge micro-03 non-claim boundary phrase(s) missing: " + ", ".join(missing)


def test_qft_gauge_micro03_lean_scaffold_has_curvature_placeholders() -> None:
    text = _read(QFT_GAUGE_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "structure Curvature",
        "structure CurvatureFromConnection",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT gauge object scaffold Lean module missing curvature placeholder token(s): " + ", ".join(
        missing
    )
