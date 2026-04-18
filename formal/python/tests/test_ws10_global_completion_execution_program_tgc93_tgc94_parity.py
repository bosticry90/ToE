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
PROGRAM_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "WS_10_GLOBAL_COMPLETION_EXECUTION_PROGRAM_20260408_v0.md"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_execution_program_pins_current_routing_pointer_and_completed_tgc93_tgc94() -> None:
    text = _read(PROGRAM_PATH)

    required_markers = [
        "CURRENT_ACTIVE_ROUTING_DECISION_POINTER_v0: formal/docs/release/WS_10_TGC_93_BRANCH_DECISION_PACKAGE_20260411_v0.md",
        "TGC-93 decision: formal/docs/release/WS_10_TGC_93_BRANCH_DECISION_PACKAGE_20260411_v0.md",
        "TGC-94 decision: formal/docs/release/WS_10_TGC_94_EM_MICRO27_AUTHORIZATION_DECISION_PACKAGE_20260418_v0.md",
        "93. TGC-93: Publish bounded branch decision package: authorize one seam reentry only with new blocker-reducing exception basis, else route to theorem-gap rework (DONE).",
        "94. TGC-94: Publish EM-local Micro-27 authorization decision package to preserve the bounded hold boundary under the qualified live theorem-gap model (DONE).",
    ]
    missing = [marker for marker in required_markers if marker not in text]
    assert not missing, "Execution program missing required TGC-93/TGC-94 parity marker(s): " + ", ".join(missing)


def test_execution_program_no_longer_marks_tgc93_as_next() -> None:
    text = _read(PROGRAM_PATH)

    assert "93. TGC-93: Publish bounded branch decision package: authorize one seam reentry only with new blocker-reducing exception basis, else route to theorem-gap rework (NEXT)." not in text