from __future__ import annotations

from pathlib import Path


REQUIRED_PHASES = [
    "TARGET_DEFINITION",
    "ASSUMPTION_FREEZE",
    "CANONICAL_ROUTE",
    "ANTI_SHORTCUT",
    "COUNTERFACTUAL",
    "INDEPENDENT_NECESSITY",
    "HARDENING",
    "BOUNDED_SCOPE",
    "DRIFT_GATES",
    "ADJUDICATION_SYNC",
]


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
CHARTER_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_TOE_QFT_SCALAR_ROUTE_v0.md"
CRITERIA_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_SCALAR_ROUTE_COMPLETION_CRITERIA_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_toe_qft_scalar_route_charter_has_required_scope_markers() -> None:
    text = _read(CHARTER_PATH)
    text_lower = text.lower()

    required_strings = [
        "Spec ID:",
        "DERIVATION_TARGET_TOE_QFT_SCALAR_ROUTE_v0",
        "Target ID:",
        "TARGET-TOE-QFT-SCALAR-ROUTE-v0",
        "Starting point:",
        "master action",
        "Comparison object:",
        "Klein-Gordon",
        "Non-claim boundary:",
        "Immediate execution packet",
    ]
    for marker in required_strings:
        assert marker in text, f"Charter missing required marker: {marker}"

    assert "no standard model unification claim" in text_lower


def test_toe_qft_scalar_route_charter_declares_architecture_phase_coverage() -> None:
    text = _read(CHARTER_PATH)
    assert "## Architecture phase coverage (v1)" in text
    for phase in REQUIRED_PHASES:
        assert f"- `{phase}`" in text, f"Missing architecture phase token: {phase}"


def test_toe_qft_scalar_route_completion_criteria_doc_is_present_and_complete() -> None:
    text = _read(CRITERIA_PATH)

    required_strings = [
        "TOE_QFT_SCALAR_ROUTE_COMPLETION_CRITERIA_v0",
        "Flagship milestone condition",
        "Klein-Gordon class",
        "quantization route",
        "non-relativistic limit",
        "Schrodinger behavior",
        "test_toe_qft_scalar_route_charter_gate.py",
    ]
    for marker in required_strings:
        assert marker in text, f"Completion criteria doc missing required marker: {marker}"
