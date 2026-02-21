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
QFT_GAUGE_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_GAUGE_OBJECT_v0.md"
QFT_GAUGE_MICRO01_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_GAUGE_MICRO_01_GROUP_ACTION_SURFACE_v0.md"
)
QFT_GAUGE_OBJECT_SCAFFOLD_LEAN_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "QFT" / "Gauge" / "ObjectScaffold.lean"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qft_gauge_micro01_artifacts_exist() -> None:
    assert QFT_GAUGE_TARGET_PATH.exists(), "Missing QFT gauge target document."
    assert QFT_GAUGE_MICRO01_PATH.exists(), "Missing QFT gauge Cycle-001 micro document."
    assert QFT_GAUGE_OBJECT_SCAFFOLD_LEAN_PATH.exists(), "Missing QFT gauge object scaffold Lean module."


def test_qft_gauge_target_references_micro01_and_gate() -> None:
    text = _read(QFT_GAUGE_TARGET_PATH)
    required_tokens = [
        "TARGET-QFT-GAUGE-MICRO-01-GROUP-ACTION-SURFACE-v0",
        "formal/docs/paper/DERIVATION_TARGET_QFT_GAUGE_MICRO_01_GROUP_ACTION_SURFACE_v0.md",
        "formal/python/tests/test_qft_gauge_micro01_group_action_surface_gate.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT gauge target document is missing required micro-01 token(s): " + ", ".join(missing)


def test_qft_gauge_micro01_contains_group_action_boundary_and_lean_pointer_tokens() -> None:
    text = _read(QFT_GAUGE_MICRO01_PATH)
    required_tokens = [
        "DERIVATION_TARGET_QFT_GAUGE_MICRO_01_GROUP_ACTION_SURFACE_v0",
        "TARGET-QFT-GAUGE-MICRO-01-GROUP-ACTION-SURFACE-v0",
        "QFT_GAUGE_MICRO01_GROUP_ACTION_ADJUDICATION: NOT_YET_DISCHARGED",
        "QFT_GAUGE_MICRO01_SCOPE_BOUNDARY_v0: GROUP_ACTION_SURFACE_ONLY_NONCLAIM",
        "QFT_GAUGE_MICRO01_PROGRESS_v0: GROUP_ACTION_SURFACE_TOKEN_PINNED",
        "QFT_GAUGE_MICRO01_GROUP_SURFACE_v0: TYPED_GROUP_OBJECT_PINNED",
        "QFT_GAUGE_MICRO01_ACTION_PLACEHOLDER_SURFACE_v0: TYPED_ACTION_PLACEHOLDER_PINNED",
        "formal/toe_formal/ToeFormal/QFT/Gauge/ObjectScaffold.lean",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT gauge micro-01 document is missing required token(s): " + ", ".join(missing)


def test_qft_gauge_micro01_nonclaim_boundary_is_explicit() -> None:
    text = _read(QFT_GAUGE_MICRO01_PATH)
    required_nonclaim_phrases = [
        "non-claim boundary is explicit and binding for this micro artifact.",
        "group/action scaffold scope only.",
        "no quantization claim.",
        "no dynamics derivation claim.",
        "no Standard Model recovery claim.",
        "no external truth claim.",
    ]
    missing = [phrase for phrase in required_nonclaim_phrases if phrase not in text]
    assert not missing, "QFT gauge micro-01 non-claim boundary phrase(s) missing: " + ", ".join(missing)
