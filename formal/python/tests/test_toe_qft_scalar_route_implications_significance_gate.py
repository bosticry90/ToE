from __future__ import annotations

import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
NOTE_REL = "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_IMPLICATIONS_SIGNIFICANCE_v0.md"
NOTE_PATH = REPO_ROOT / NOTE_REL

REQUIRED_HEADINGS = (
    "## 1. Supported Now",
    "## 2. Reconstructed Core",
    "## 3. Route-Level Novelty",
    "## 4. Open Items And Blockers",
    "## 5. What This Does And Does Not Say About Bigger Physics Questions",
    "## 6. Next Seam-First Target",
    "## 7. Plain-Language Explanation",
    "## 8. Non-Claim Boundary",
)

REQUIRED_AUTHORITY_POINTERS = (
    "State_of_the_Theory.md",
    "formal/docs/paper/PHYSICS_ROADMAP_v0.md",
    "formal/docs/paper/DERIVATION_TARGET_TOE_QFT_SCALAR_ROUTE_v0.md",
    "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_REVIEW_READINESS_v0.md",
    "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_MILESTONE_SUMMARY_v0.md",
    "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_SUBMISSION_READINESS_NOTE_v0.md",
    "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_MANUSCRIPT_DRAFT_v0.md",
)

REQUIRED_NONCLAIM_PHRASES = (
    "does not claim interacting-field completion",
    "does not claim gauge completion",
    "does not claim full unification",
    "does not claim dark matter",
    "does not claim dark energy",
)

FORBIDDEN_OVERCLAIM_PATTERNS = (
    r"interacting-field completion\s+(is\s+)?(achieved|complete)",
    r"gauge(-sector)?\s+completion\s+(is\s+)?(achieved|complete)",
    r"full\s+unification\s+(is\s+)?(achieved|complete)",
    r"dark\s+matter\s+(is\s+)?explained",
    r"dark\s+energy\s+(is\s+)?explained",
)


def load_note() -> str:
    return NOTE_PATH.read_text(encoding="utf-8")


def test_implications_note_exists() -> None:
    assert NOTE_PATH.exists(), f"Missing implications note: {NOTE_REL}"


def test_implications_note_contains_required_headings() -> None:
    text = load_note()
    for heading in REQUIRED_HEADINGS:
        assert heading in text, f"Missing required heading: {heading}"


def test_implications_note_contains_required_authority_pointers() -> None:
    text = load_note()
    for ptr in REQUIRED_AUTHORITY_POINTERS:
        assert ptr in text, f"Missing required authority pointer: {ptr}"


def test_implications_note_contains_explicit_nonclaim_wording() -> None:
    text = load_note().lower()
    for phrase in REQUIRED_NONCLAIM_PHRASES:
        assert phrase in text, f"Missing required non-claim wording: {phrase}"


def test_implications_note_has_no_forbidden_overclaim_language() -> None:
    text = load_note().lower()
    for pattern in FORBIDDEN_OVERCLAIM_PATTERNS:
        assert re.search(pattern, text) is None, (
            "Forbidden overclaim language found in implications note "
            f"for pattern: {pattern}"
        )
