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
QFT_GAUGE_MICRO05_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_QFT_GAUGE_MICRO_05_COUPLING_SOURCE_CURRENT_INTERFACE_v0.md"
)
QFT_GAUGE_OBJECT_SCAFFOLD_LEAN_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "QFT" / "Gauge" / "ObjectScaffold.lean"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qft_gauge_micro05_artifacts_exist() -> None:
    assert QFT_GAUGE_TARGET_PATH.exists(), "Missing QFT gauge target document."
    assert QFT_GAUGE_MICRO05_PATH.exists(), "Missing QFT gauge Cycle-005 micro document."
    assert QFT_GAUGE_OBJECT_SCAFFOLD_LEAN_PATH.exists(), "Missing QFT gauge object scaffold Lean module."


def test_qft_gauge_target_references_micro05_and_gate() -> None:
    text = _read(QFT_GAUGE_TARGET_PATH)
    required_tokens = [
        "TARGET-QFT-GAUGE-MICRO-05-COUPLING-SOURCE-CURRENT-INTERFACE-v0",
        "formal/docs/paper/DERIVATION_TARGET_QFT_GAUGE_MICRO_05_COUPLING_SOURCE_CURRENT_INTERFACE_v0.md",
        "formal/python/tests/test_qft_gauge_micro05_coupling_source_current_interface_gate.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT gauge target document is missing required micro-05 token(s): " + ", ".join(missing)


def test_qft_gauge_micro05_contains_coupling_boundary_and_lean_pointer_tokens() -> None:
    text = _read(QFT_GAUGE_MICRO05_PATH)
    required_tokens = [
        "DERIVATION_TARGET_QFT_GAUGE_MICRO_05_COUPLING_SOURCE_CURRENT_INTERFACE_v0",
        "TARGET-QFT-GAUGE-MICRO-05-COUPLING-SOURCE-CURRENT-INTERFACE-v0",
        "QFT_GAUGE_MICRO05_COUPLING_ADJUDICATION: NOT_YET_DISCHARGED",
        "QFT_GAUGE_MICRO05_SCOPE_BOUNDARY_v0: COUPLING_INTERFACE_ONLY_NONCLAIM",
        "QFT_GAUGE_MICRO05_PROGRESS_v0: COUPLING_INTERFACE_TOKEN_PINNED",
        "QFT_GAUGE_MICRO05_COUPLING_SURFACE_v0: CURRENT_SOURCE_INTERFACE_STATEMENT_ONLY",
        "formal/toe_formal/ToeFormal/QFT/Gauge/ObjectScaffold.lean",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT gauge micro-05 document is missing required token(s): " + ", ".join(missing)


def test_qft_gauge_micro05_nonclaim_boundary_is_explicit() -> None:
    text = _read(QFT_GAUGE_MICRO05_PATH)
    required_nonclaim_phrases = [
        "coupling interface scaffold scope only.",
        "statement-only interface (no dynamics equation, no closure).",
        "no quantization claim.",
        "no dynamics derivation claim.",
        "no Standard Model recovery claim.",
        "no external truth claim.",
    ]
    missing = [phrase for phrase in required_nonclaim_phrases if phrase not in text]
    assert not missing, "QFT gauge micro-05 non-claim boundary phrase(s) missing: " + ", ".join(missing)


def test_qft_gauge_micro05_lean_scaffold_has_coupling_statement_tokens() -> None:
    text = _read(QFT_GAUGE_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "structure CurrentSourceInterface",
        "def couplingStatementOnly",
        "theorem couplingStatementOnly_holds",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, (
        "QFT gauge object scaffold Lean module missing coupling statement token(s): "
        + ", ".join(missing)
    )
