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
QFT_GAUGE_MICRO04_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_QFT_GAUGE_MICRO_04_GAUGE_TRANSFORM_INVARIANCE_SURFACE_v0.md"
)
QFT_GAUGE_OBJECT_SCAFFOLD_LEAN_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "QFT" / "Gauge" / "ObjectScaffold.lean"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qft_gauge_micro04_artifacts_exist() -> None:
    assert QFT_GAUGE_TARGET_PATH.exists(), "Missing QFT gauge target document."
    assert QFT_GAUGE_MICRO04_PATH.exists(), "Missing QFT gauge Cycle-004 micro document."
    assert QFT_GAUGE_OBJECT_SCAFFOLD_LEAN_PATH.exists(), "Missing QFT gauge object scaffold Lean module."


def test_qft_gauge_target_references_micro04_and_gate() -> None:
    text = _read(QFT_GAUGE_TARGET_PATH)
    required_tokens = [
        "TARGET-QFT-GAUGE-MICRO-04-GAUGE-TRANSFORM-INVARIANCE-SURFACE-v0",
        "formal/docs/paper/DERIVATION_TARGET_QFT_GAUGE_MICRO_04_GAUGE_TRANSFORM_INVARIANCE_SURFACE_v0.md",
        "formal/python/tests/test_qft_gauge_micro04_gauge_transform_invariance_surface_gate.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT gauge target document is missing required micro-04 token(s): " + ", ".join(missing)


def test_qft_gauge_micro04_contains_transform_invariance_boundary_and_lean_pointer_tokens() -> None:
    text = _read(QFT_GAUGE_MICRO04_PATH)
    required_tokens = [
        "DERIVATION_TARGET_QFT_GAUGE_MICRO_04_GAUGE_TRANSFORM_INVARIANCE_SURFACE_v0",
        "TARGET-QFT-GAUGE-MICRO-04-GAUGE-TRANSFORM-INVARIANCE-SURFACE-v0",
        "QFT_GAUGE_MICRO04_TRANSFORM_INVARIANCE_ADJUDICATION: NOT_YET_DISCHARGED",
        "QFT_GAUGE_MICRO04_SCOPE_BOUNDARY_v0: TRANSFORM_INVARIANCE_SURFACE_ONLY_NONCLAIM",
        "QFT_GAUGE_MICRO04_PROGRESS_v0: TRANSFORM_INVARIANCE_SURFACE_TOKEN_PINNED",
        "QFT_GAUGE_MICRO04_GAUGE_TRANSFORM_SURFACE_v0: GAUGE_TRANSFORM_STATEMENT_ONLY",
        "QFT_GAUGE_MICRO04_INVARIANCE_SURFACE_v0: INVARIANCE_STATEMENT_ONLY",
        "formal/toe_formal/ToeFormal/QFT/Gauge/ObjectScaffold.lean",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT gauge micro-04 document is missing required token(s): " + ", ".join(missing)


def test_qft_gauge_micro04_nonclaim_boundary_is_explicit() -> None:
    text = _read(QFT_GAUGE_MICRO04_PATH)
    required_nonclaim_phrases = [
        "transform/invariance scaffold scope only.",
        "statement-only invariance (no proof/closure).",
        "no dynamics derivation claim.",
        "no quantization claim.",
        "no Standard Model recovery claim.",
        "no external truth claim.",
    ]
    missing = [phrase for phrase in required_nonclaim_phrases if phrase not in text]
    assert not missing, "QFT gauge micro-04 non-claim boundary phrase(s) missing: " + ", ".join(missing)


def test_qft_gauge_micro04_lean_scaffold_has_transform_statement_tokens() -> None:
    text = _read(QFT_GAUGE_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "def GaugeTransform",
        "def gaugeTransformStatementOnly",
        "theorem gaugeTransformStatementOnly_holds",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, (
        "QFT gauge object scaffold Lean module missing transform/invariance statement token(s): "
        + ", ".join(missing)
    )
